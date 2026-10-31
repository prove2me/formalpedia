-- Prove2me | solution 1 for FiniteEnergyPlane.exists_smooth_periodic_root_family
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-30T09:54:28.390441+00:00
-- url     : https://prove2.me/submissions/c41f0ba4-3224-4c73-8091-00216c808a02

import Mathlib



namespace FiniteEnergyPlane

open Metric

theorem exists_norm_le_mul_norm_of_periodic_aux {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (Φ : ℝ × E → F) (T r : ℝ) (hT : 0 < T) (hr : 0 < r)
    (hΦ : ContDiffOn ℝ 1 Φ (Set.univ ×ˢ ball (0 : E) r))
    (hper : ∀ (φ : ℝ) (v : E), ‖v‖ < r → Φ (φ + T, v) = Φ (φ, v))
    (h0 : ∀ φ : ℝ, Φ (φ, 0) = 0) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ (φ : ℝ) (v : E), ‖v‖ ≤ r / 2 → ‖Φ (φ, v)‖ ≤ L * ‖v‖ := by
  have hU : IsOpen ((Set.univ : Set ℝ) ×ˢ ball (0 : E) r) := isOpen_univ.prod isOpen_ball
  have hcont : ContinuousOn (fderiv ℝ Φ) (Set.univ ×ˢ ball (0 : E) r) :=
    hΦ.continuousOn_fderiv_of_isOpen hU le_rfl
  have hK : IsCompact (Set.Icc 0 T ×ˢ closedBall (0 : E) (r / 2)) :=
    isCompact_Icc.prod (isCompact_closedBall _ _)
  have hKU : Set.Icc 0 T ×ˢ closedBall (0 : E) (r / 2) ⊆ Set.univ ×ˢ ball (0 : E) r :=
    Set.prod_mono (Set.subset_univ _) (closedBall_subset_ball (by linarith))
  obtain ⟨L₀, hL₀⟩ := hK.exists_bound_of_continuousOn (hcont.mono hKU)
  refine ⟨max L₀ 0, le_max_right _ _, fun φ v hv => ?_⟩
  have hvr : ‖v‖ < r := by linarith
  have hpf : Function.Periodic (fun ψ => Φ (ψ, v)) T := fun ψ => hper ψ v hvr
  obtain ⟨φ', hφ', hfφ⟩ := hpf.exists_mem_Ico₀ hT φ
  rw [show Φ (φ, v) = Φ (φ', v) from hfφ]
  set s := ({φ'} : Set ℝ) ×ˢ closedBall (0 : E) (r / 2) with hs
  have hsK : s ⊆ Set.Icc 0 T ×ˢ closedBall (0 : E) (r / 2) :=
    Set.prod_mono (Set.singleton_subset_iff.2 (Set.Ico_subset_Icc_self hφ')) le_rfl
  have hdiff : ∀ q ∈ s, DifferentiableAt ℝ Φ q := fun q hq =>
    ((hΦ.differentiableOn (by simp)) q (hKU (hsK hq))).differentiableAt
      (hU.mem_nhds (hKU (hsK hq)))
  have hbound : ∀ q ∈ s, ‖fderiv ℝ Φ q‖ ≤ max L₀ 0 := fun q hq =>
    (hL₀ q (hsK hq)).trans (le_max_left _ _)
  have hconv : Convex ℝ s := (convex_singleton _).prod (convex_closedBall _ _)
  have hx : ((φ', (0 : E)) : ℝ × E) ∈ s := ⟨rfl, by simp; linarith⟩
  have hy : ((φ', v) : ℝ × E) ∈ s := ⟨rfl, by simpa using hv⟩
  have key := hconv.norm_image_sub_le_of_norm_fderiv_le hdiff hbound hx hy
  rw [h0, sub_zero] at key
  have hn : ‖((φ', v) : ℝ × E) - (φ', 0)‖ = ‖v‖ := by simp [Prod.norm_def]
  rwa [hn] at key

end FiniteEnergyPlane

namespace FiniteEnergyPlane

open Metric Filter Topology
open scoped ContDiff

/-- A continuous `T`-periodic positive function has a positive lower bound. -/
lemma ktr_periodic_lb {f : ℝ → ℝ} {T : ℝ} (hT : 0 < T) (hf : Continuous f)
    (hper : Function.Periodic f T) (hpos : ∀ x, 0 < f x) : ∃ m > 0, ∀ x, m ≤ f x := by
  obtain ⟨x₀, -, hmin⟩ :=
    isCompact_Icc.exists_isMinOn (Set.nonempty_Icc.2 hT.le) hf.continuousOn
  refine ⟨f x₀, hpos x₀, fun x => ?_⟩
  obtain ⟨y, hy, hfy⟩ := hper.exists_mem_Ico₀ hT x
  rw [hfy]
  exact hmin (Set.Ico_subset_Icc_self hy)

/-- One-dimensional root in a window: `f' ≥ c > 0` on `[-η, η]` and `|f 0| < c η`. -/
lemma ktr_root_1d {f : ℝ → ℝ} (hf : Differentiable ℝ f) {η c : ℝ} (hη : 0 < η) (hc : 0 < c)
    (hd : ∀ σ, |σ| ≤ η → c ≤ deriv f σ) (h0 : |f 0| < c * η) :
    ∃ σ, |σ| < η ∧ f σ = 0 ∧ ∀ σ', |σ'| < η → f σ' = 0 → σ' = σ := by
  have hD : Convex ℝ (Set.Icc (-η) η) := convex_Icc _ _
  have hge : ∀ x ∈ interior (Set.Icc (-η) η), c ≤ deriv f x := by
    rw [interior_Icc]; intro x hx; exact hd x (abs_le.2 ⟨hx.1.le, hx.2.le⟩)
  have hmvt := hD.mul_sub_le_image_sub_of_le_deriv hf.continuous.continuousOn
    hf.differentiableOn hge
  have hmem : ∀ σ, |σ| ≤ η → σ ∈ Set.Icc (-η) η := fun σ h => abs_le.1 h
  have h0m : (0 : ℝ) ∈ Set.Icc (-η) η := hmem 0 (by simp [hη.le])
  have hηm : η ∈ Set.Icc (-η) η := hmem η (by rw [abs_of_pos hη])
  have hηm' : -η ∈ Set.Icc (-η) η := hmem (-η) (by rw [abs_neg, abs_of_pos hη])
  have h1 := hmvt 0 h0m η hηm hη.le
  have h2 := hmvt (-η) hηm' 0 h0m (by linarith)
  have h0' := abs_lt.1 h0
  have hpos : 0 < f η := by nlinarith
  have hneg : f (-η) < 0 := by nlinarith
  obtain ⟨σ, hσ, hfσ⟩ := intermediate_value_Ioo (by linarith : -η ≤ η)
    hf.continuous.continuousOn ⟨hneg, hpos⟩
  have hσa : |σ| < η := abs_lt.2 ⟨hσ.1, hσ.2⟩
  refine ⟨σ, hσa, hfσ, fun σ' hσ' hf' => ?_⟩
  have hσ'm := hmem σ' hσ'.le
  have hσm := hmem σ hσa.le
  rcases lt_trichotomy σ' σ with h | h | h
  · have := hmvt σ' hσ'm σ hσm h.le
    rw [hfσ, hf'] at this; nlinarith
  · exact h
  · have := hmvt σ hσm σ' hσ'm h.le
    rw [hfσ, hf'] at this; nlinarith

lemma ktr_isInvertible (L : ℝ →L[ℝ] ℝ) (h : L 1 ≠ 0) : L.IsInvertible := by
  refine ⟨ContinuousLinearEquiv.unitsEquivAut ℝ (Units.mk0 (L 1) h), ?_⟩
  ext
  simp

theorem exists_smooth_periodic_root_family_aux {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] (G : (ℝ × E) × ℝ → ℝ) (hG : ContDiff ℝ ∞ G)
    (T : ℝ) (hT : 0 < T)
    (hper : ∀ (φ : ℝ) (v : E) (σ : ℝ), G ((φ + T, v), σ) = G ((φ, v), σ))
    (h0 : ∀ φ : ℝ, G ((φ, 0), 0) = 0)
    (hd : ∀ φ : ℝ, deriv (fun σ : ℝ => G ((φ, 0), σ)) 0 ≠ 0)
    (δ₀ : ℝ) (hδ₀ : 0 < δ₀) :
    ∃ δ r : ℝ, 0 < δ ∧ δ ≤ δ₀ ∧ 0 < r ∧ ∃ g : ℝ × E → ℝ,
      ContDiffOn ℝ ∞ g (Set.univ ×ˢ ball (0 : E) r) ∧
      (∀ (φ : ℝ) (v : E), g (φ + T, v) = g (φ, v)) ∧ (∀ φ : ℝ, g (φ, 0) = 0) ∧
      ∀ (φ : ℝ) (v : E), ‖v‖ < r →
        |g (φ, v)| < δ ∧ G ((φ, v), g (φ, v)) = 0 ∧
        ∀ σ : ℝ, |σ| < δ → G ((φ, v), σ) = 0 → σ = g (φ, v) := by
  classical
  -- the `σ`-derivative
  obtain ⟨dG, hdG⟩ : ∃ dG : (ℝ × E) × ℝ → ℝ, ∀ q, dG q = fderiv ℝ G q ((0 : ℝ × E), (1 : ℝ)) :=
    ⟨_, fun _ => rfl⟩
  have hdGc : Continuous dG := by
    have : dG = fun q => fderiv ℝ G q ((0 : ℝ × E), (1 : ℝ)) := funext hdG
    rw [this]; exact (hG.continuous_fderiv (by simp)).clm_apply continuous_const
  have hderiv : ∀ (q : ℝ × E) (σ : ℝ), HasDerivAt (fun σ' => G (q, σ')) (dG (q, σ)) σ := by
    intro q σ
    have h1 : HasDerivAt (fun σ' : ℝ => ((q, σ') : (ℝ × E) × ℝ)) ((0 : ℝ × E), (1 : ℝ)) σ :=
      (hasDerivAt_const σ q).prodMk (hasDerivAt_id σ)
    rw [hdG]
    exact ((hG.differentiable (by simp)) (q, σ)).hasFDerivAt.comp_hasDerivAt σ h1
  -- the slice functions are periodic in `φ`
  have hfun : ∀ (φ : ℝ) (v : E), ∃ φ' ∈ Set.Icc 0 T,
      (fun σ => G ((φ, v), σ)) = fun σ => G ((φ', v), σ) := by
    intro φ v
    have hp : Function.Periodic (fun ψ => fun σ => G ((ψ, v), σ)) T :=
      fun ψ => funext fun σ => hper ψ v σ
    obtain ⟨φ', hφ', h⟩ := hp.exists_mem_Ico₀ hT φ
    exact ⟨φ', Set.Ico_subset_Icc_self hφ', h⟩
  have hdG_eq : ∀ (φ φ' : ℝ) (v : E), (fun σ => G ((φ, v), σ)) = (fun σ => G ((φ', v), σ)) →
      ∀ σ, dG ((φ, v), σ) = dG ((φ', v), σ) := by
    intro φ φ' v h σ
    rw [← (hderiv (φ, v) σ).deriv, ← (hderiv (φ', v) σ).deriv]
    exact congrArg (fun f => deriv f σ) h
  -- `k(φ) = ∂_σ G((φ,0),0)` is bounded away from `0`
  have hk : ∀ φ, dG ((φ, 0), 0) ≠ 0 := fun φ => by
    rw [← (hderiv (φ, 0) 0).deriv]; exact hd φ
  obtain ⟨m, hm, hmk⟩ := ktr_periodic_lb hT
    (continuous_abs.comp (hdGc.comp (by fun_prop : Continuous fun φ : ℝ => (((φ, (0 : E)), (0 : ℝ)) : (ℝ × E) × ℝ))))
    (fun φ => by
      simp only [Function.comp_apply]
      rw [hdG_eq (φ + T) φ 0 (funext fun σ => hper φ 0 σ)])
    (fun φ => abs_pos.2 (hk φ))
  simp only [Function.comp_apply] at hmk
  -- uniform continuity of `dG` on a compact box
  set K := (Set.Icc 0 T ×ˢ closedBall (0 : E) 1) ×ˢ Set.Icc (-1 : ℝ) 1 with hK
  have hKc : IsCompact K := (isCompact_Icc.prod (isCompact_closedBall _ _)).prod isCompact_Icc
  obtain ⟨ρ, hρ, hρK⟩ := Metric.uniformContinuousOn_iff.1
    (hKc.uniformContinuousOn_of_continuous hdGc.continuousOn) (m / 2) (half_pos hm)
  set η := min (min (ρ / 2) 1) δ₀ with hη
  have hη0 : 0 < η := lt_min (lt_min (half_pos hρ) one_pos) hδ₀
  have hη1 : η ≤ 1 := (min_le_left _ _).trans (min_le_right _ _)
  have hηρ : η < ρ := lt_of_le_of_lt ((min_le_left _ _).trans (min_le_left _ _)) (half_lt_self hρ)
  have hclose : ∀ φ ∈ Set.Icc 0 T, ∀ v : E, ‖v‖ ≤ η → ∀ σ : ℝ, |σ| ≤ η →
      |dG ((φ, v), σ) - dG ((φ, 0), 0)| < m / 2 := by
    intro φ hφ v hv σ hσ
    have hx : ((φ, v), σ) ∈ K :=
      ⟨⟨hφ, by rw [mem_closedBall_zero_iff]; exact hv.trans hη1⟩, abs_le.1 (hσ.trans hη1)⟩
    have hy : ((φ, (0 : E)), (0 : ℝ)) ∈ K :=
      ⟨⟨hφ, by simp⟩, by simp⟩
    have hdist : dist ((φ, v), σ) ((φ, (0 : E)), (0 : ℝ)) < ρ := by
      rw [Prod.dist_eq, Prod.dist_eq, dist_self]
      refine max_lt (max_lt hρ ?_) ?_
      · rw [dist_zero_right]; linarith
      · rw [Real.dist_eq, sub_zero]; linarith
    have := hρK _ hx _ hy hdist
    rwa [Real.dist_eq] at this
  -- `|G((φ, v), 0)| ≤ L ‖v‖`
  obtain ⟨LG, hLG0, hLG⟩ := exists_norm_le_mul_norm_of_periodic_aux
    (fun q : ℝ × E => G (q, 0)) T 2 hT two_pos
    ((hG.comp (contDiff_id.prodMk contDiff_const)).contDiffOn.of_le (by simp))
    (fun φ v _ => hper φ v 0) h0
  set r := min η (m * η / (2 * (LG + 1))) with hr
  have hr0 : 0 < r := lt_min hη0 (div_pos (mul_pos hm hη0) (by linarith))
  have hrη : r ≤ η := min_le_left _ _
  have hG0small : ∀ (φ : ℝ) (v : E), ‖v‖ < r → |G ((φ, v), 0)| < m / 2 * η := by
    intro φ v hv
    have h1 := hLG φ v (by linarith)
    rw [Real.norm_eq_abs] at h1
    have h2 : ‖v‖ < m * η / (2 * (LG + 1)) := lt_of_lt_of_le hv (min_le_right _ _)
    have h3 : (LG + 1) * ‖v‖ < (LG + 1) * (m * η / (2 * (LG + 1))) :=
      mul_lt_mul_of_pos_left h2 (by linarith)
    have h4 : (LG + 1) * (m * η / (2 * (LG + 1))) = m / 2 * η := by field_simp
    nlinarith [norm_nonneg v]
  -- unique root at `φ ∈ [0, T]`, then for all `φ`
  have hcore0 : ∀ φ ∈ Set.Icc 0 T, ∀ v : E, ‖v‖ < r → ∃ σ, |σ| < η ∧ G ((φ, v), σ) = 0 ∧
      ∀ σ', |σ'| < η → G ((φ, v), σ') = 0 → σ' = σ := by
    intro φ hφ v hv
    have hdiff : Differentiable ℝ (fun σ => G ((φ, v), σ)) :=
      fun σ => (hderiv (φ, v) σ).differentiableAt
    have hcl : ∀ σ, |σ| ≤ η → |dG ((φ, v), σ) - dG ((φ, 0), 0)| < m / 2 :=
      fun σ hσ => hclose φ hφ v (by linarith) σ hσ
    have hmk' := hmk φ
    rcases lt_or_gt_of_ne (hk φ) with hneg | hpos
    · rw [abs_of_neg hneg] at hmk'
      obtain ⟨σ, hσ, hf, hu⟩ := ktr_root_1d (f := fun σ => -G ((φ, v), σ)) hdiff.neg hη0
        (half_pos hm) (fun σ hσ => by
          rw [show (fun σ => -G ((φ, v), σ)) = -(fun σ => G ((φ, v), σ)) from rfl, deriv.neg,
            (hderiv (φ, v) σ).deriv]
          have := (abs_lt.1 (hcl σ hσ)).2
          linarith)
        (by simpa [abs_neg] using hG0small φ v hv)
      exact ⟨σ, hσ, neg_eq_zero.1 hf, fun σ' h1 h2 => hu σ' h1 (by simp [h2])⟩
    · rw [abs_of_pos hpos] at hmk'
      exact ktr_root_1d hdiff hη0 (half_pos hm)
        (fun σ hσ => by
          rw [(hderiv (φ, v) σ).deriv]
          have := (abs_lt.1 (hcl σ hσ)).1
          linarith)
        (hG0small φ v hv)
  have hcore : ∀ (φ : ℝ) (v : E), ‖v‖ < r → ∃ σ, |σ| < η ∧ G ((φ, v), σ) = 0 ∧
      ∀ σ', |σ'| < η → G ((φ, v), σ') = 0 → σ' = σ := by
    intro φ v hv
    obtain ⟨φ', hφ', hfe⟩ := hfun φ v
    obtain ⟨σ, h1, h2, h3⟩ := hcore0 φ' hφ' v hv
    have e : ∀ σ, G ((φ, v), σ) = G ((φ', v), σ) := fun σ => congrFun hfe σ
    exact ⟨σ, h1, by rw [e]; exact h2, fun σ' a b => h3 σ' a (by rw [← e]; exact b)⟩
  -- the root function
  let g : ℝ × E → ℝ := fun q => if h : ‖q.2‖ < r then Classical.choose (hcore q.1 q.2 h) else 0
  have hgspec : ∀ (φ : ℝ) (v : E), ‖v‖ < r → |g (φ, v)| < η ∧ G ((φ, v), g (φ, v)) = 0 ∧
      ∀ σ', |σ'| < η → G ((φ, v), σ') = 0 → σ' = g (φ, v) := by
    intro φ v hv
    have := Classical.choose_spec (hcore φ v hv)
    simp only [g, dif_pos hv]
    exact this
  have hgper : ∀ (φ : ℝ) (v : E), g (φ + T, v) = g (φ, v) := by
    intro φ v
    by_cases hv : ‖v‖ < r
    · obtain ⟨h1, h2, -⟩ := hgspec (φ + T) v hv
      obtain ⟨-, -, h3⟩ := hgspec φ v hv
      exact h3 _ h1 (by rw [← hper]; exact h2)
    · simp only [g, dif_neg hv]
  have hg0 : ∀ φ : ℝ, g (φ, 0) = 0 := by
    intro φ
    obtain ⟨-, -, h3⟩ := hgspec φ 0 (by simpa using hr0)
    exact (h3 0 (by simpa using hη0) (h0 φ)).symm
  refine ⟨η, r, hη0, min_le_right _ _, hr0, g, ?_, hgper, hg0, hgspec⟩
  -- smoothness, from the local implicit function and uniqueness
  have hopen : IsOpen ((Set.univ : Set ℝ) ×ˢ ball (0 : E) r) := isOpen_univ.prod isOpen_ball
  intro q₀ hq₀
  refine ContDiffAt.contDiffWithinAt ?_
  obtain ⟨φ₀, v₀⟩ := q₀
  have hv₀ : ‖v₀‖ < r := by simpa using hq₀.2
  obtain ⟨hgη, hgG, -⟩ := hgspec φ₀ v₀ hv₀
  set u : (ℝ × E) × ℝ := ((φ₀, v₀), g (φ₀, v₀)) with hu
  have hcdf : ContDiffAt ℝ ∞ G u := hG.contDiffAt
  have hpn : (∞ : WithTop ℕ∞) ≠ 0 := by simp
  have hne : dG u ≠ 0 := by
    obtain ⟨φ', hφ', hfe⟩ := hfun φ₀ v₀
    rw [hu, hdG_eq φ₀ φ' v₀ hfe]
    have h1 := hclose φ' hφ' v₀ (by linarith) _ (by linarith)
    have h2 := hmk φ'
    intro h0'
    rw [h0', zero_sub, abs_neg] at h1
    linarith
  have hinv : (fderiv ℝ G u ∘L ContinuousLinearMap.inr ℝ (ℝ × E) ℝ).IsInvertible := by
    apply ktr_isInvertible
    simpa [hdG] using hne
  set ψ := hcdf.implicitFunction hpn hinv with hψ
  have hψ0 : ψ (φ₀, v₀) = g (φ₀, v₀) := hcdf.implicitFunction_apply_self hpn hinv
  have hψc : ContDiffAt ℝ ∞ ψ (φ₀, v₀) := hcdf.contDiffAt_implicitFunction hpn hinv
  have hψG : ∀ᶠ q in 𝓝 (φ₀, v₀), G (q, ψ q) = G u := hcdf.eventually_apply_implicitFunction hpn hinv
  have hψη : ∀ᶠ q in 𝓝 (φ₀, v₀), |ψ q| < η := by
    have : ContinuousAt (fun q => |ψ q|) (φ₀, v₀) := continuous_abs.continuousAt.comp hψc.continuousAt
    exact this.eventually (gt_mem_nhds (by show |ψ (φ₀, v₀)| < η; rw [hψ0]; exact hgη))
  have hball : ∀ᶠ q in 𝓝 ((φ₀, v₀) : ℝ × E), ‖q.2‖ < r :=
    (continuous_norm.comp continuous_snd).continuousAt.eventually (gt_mem_nhds hv₀)
  refine hψc.congr_of_eventuallyEq ?_
  filter_upwards [hψG, hψη, hball] with q h1 h2 h3
  obtain ⟨φ, v⟩ := q
  obtain ⟨-, -, h4⟩ := hgspec φ v h3
  rw [hu, hgG] at h1
  exact (h4 _ h2 h1).symm

end FiniteEnergyPlane

open FiniteEnergyPlane

open Metric
open scoped ContDiff

theorem solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (G : (ℝ × E) × ℝ → ℝ) (hG : ContDiff ℝ ∞ G) (T : ℝ) (hT : 0 < T)
    (hper : ∀ (φ : ℝ) (v : E) (σ : ℝ), G ((φ + T, v), σ) = G ((φ, v), σ))
    (h0 : ∀ φ : ℝ, G ((φ, 0), 0) = 0)
    (hd : ∀ φ : ℝ, deriv (fun σ : ℝ => G ((φ, 0), σ)) 0 ≠ 0)
    (δ₀ : ℝ) (hδ₀ : 0 < δ₀) :
    ∃ δ r : ℝ, 0 < δ ∧ δ ≤ δ₀ ∧ 0 < r ∧ ∃ g : ℝ × E → ℝ,
      ContDiffOn ℝ ∞ g (Set.univ ×ˢ ball (0 : E) r) ∧
      (∀ (φ : ℝ) (v : E), g (φ + T, v) = g (φ, v)) ∧ (∀ φ : ℝ, g (φ, 0) = 0) ∧
      ∀ (φ : ℝ) (v : E), ‖v‖ < r →
        |g (φ, v)| < δ ∧ G ((φ, v), g (φ, v)) = 0 ∧
        ∀ σ : ℝ, |σ| < δ → G ((φ, v), σ) = 0 → σ = g (φ, v) :=
  exists_smooth_periodic_root_family_aux G hG T hT hper h0 hd δ₀ hδ₀
