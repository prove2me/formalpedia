-- Prove2me | solution 1 for FiniteEnergyPlane.exists_norm_le_of_pageMap_mem
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-25T13:47:52.052657+00:00
-- url     : https://prove2.me/submissions/034acb06-adea-448f-9a2c-77f525a943be

import Definitions.Def_FiniteEnergyPlane_OpenBook
import Mathlib
import Theorems.Thm_FiniteEnergyPlane_proj_mem_energySurface
import Theorems.Thm_FiniteEnergyPlane_proj_smul_eq_of_mem_energySurface
import Theorems.Thm_FiniteEnergyPlane_contDiffOn_pageMap
import Theorems.Thm_FiniteEnergyPlane_dlambdaEnergy_univ_eq_of_isNondegenerateEnd
import Theorems.Thm_FiniteEnergyPlane_eventually_lt_dlambdaEnergy_slice
import Theorems.Thm_FiniteEnergyPlane_exists_isReebTrajectory
import Theorems.Thm_FiniteEnergyPlane_exists_local_page_family
import Theorems.Thm_FiniteEnergyPlane_exists_mem_embeddedFastPlaneSet_of_isEmbeddedPlane
import Theorems.Thm_FiniteEnergyPlane_exists_radius_lt_dlambdaEnergy_ball
import Theorems.Thm_FiniteEnergyPlane_exists_shiftA_comp_affine_of_range_eq
import Theorems.Thm_FiniteEnergyPlane_injOn_pageMap_of_isPageFamilyOn
import Theorems.Thm_FiniteEnergyPlane_injective_fderiv_pageMap_of_isPageFamilyOn
import Theorems.Thm_FiniteEnergyPlane_nhdsWithin_energySurface_le_map
import Theorems.Thm_FiniteEnergyPlane_norm_lt_of_affine_of_dlambdaEnergy_lt
import Theorems.Thm_FiniteEnergyPlane_proj_aCoord_exp_smul
import Theorems.Thm_FiniteEnergyPlane_range_eq_of_proj_eq_of_mem_embeddedFastPlaneSet



namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

lemma pfo_ne_zero {n : ℕ} {H : V n → ℝ} (hH : IsStrictlyStarShapedLevel H) {x : V n}
    (hx : H x = 1) : x ≠ 0 := by
  rintro rfl
  have := hH.2.2 0 hx
  simp at this

lemma pfo_proj_mem {n : ℕ} {H : V n → ℝ} (hH : IsStrictlyStarShapedLevel H) {y : V n} (hy : y ≠ 0) :
    H (proj H y) = 1 := proj_mem_energySurface H hH y hy

lemma pfo_proj_smul {n : ℕ} {H : V n → ℝ} (hH : IsStrictlyStarShapedLevel H) {x : V n}
    (hx : H x = 1) {r : ℝ} (hr : 0 < r) : proj H (r • x) = x :=
  proj_smul_eq_of_mem_energySurface H hH x hx r hr

lemma pfo_proj_self {n : ℕ} {H : V n → ℝ} (hH : IsStrictlyStarShapedLevel H) {x : V n}
    (hx : H x = 1) : proj H x = x := by
  simpa using pfo_proj_smul hH hx one_pos

lemma pfo_eq_smul {n : ℕ} {H : V n → ℝ} (hH : IsStrictlyStarShapedLevel H) {y : V n}
    (hy : y ≠ 0) : ∃ r : ℝ, y = Real.exp r • proj H y := by
  obtain ⟨s, hs, hsy⟩ := (hH.2.1 _ hy).exists
  refine ⟨-Real.log s, ?_⟩
  have h := pfo_proj_smul hH hsy (inv_pos.2 hs)
  rw [smul_smul, inv_mul_cancel₀ hs.ne', one_smul] at h
  rw [h, Real.exp_neg, Real.exp_log hs, smul_smul, inv_mul_cancel₀ hs.ne', one_smul]

lemma pfo_smul_eq {n : ℕ} {H : V n → ℝ} (hH : IsStrictlyStarShapedLevel H) {x q : V n} {r : ℝ}
    (hx : H x = 1) (hq : H q = 1) (h : Real.exp r • x = q) : x = q := by
  rw [← pfo_proj_smul hH hx (Real.exp_pos r), h, pfo_proj_self hH hq]

end FiniteEnergyPlane

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem exists_norm_le_of_pageMap_mem_aux (H : V 1 → ℝ)
    (hH : IsStrictlyStarShapedLevel H)
    (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J)
    (P : ReebOrbit H) (hcz : P.IsCZAtLeast 3) (γ : ℝ) (hγ : 0 < γ) (hγT : γ < P.T)
    (hΛ : ∀ K : Set (V 1), IsCompact K → (0 : V 1) ∉ K → (∀ y ∈ K, proj H y ∉ Set.range P.x) →
      IsSeqCompactCInftyLoc (embeddedFastPlaneSet H J P K γ))
    (y : ℝ → V 1) (hy : IsReebTrajectory H y)
    (l : ℕ) (hl : 1 ≤ l) (I : Set ℝ) (hI : IsOpen I) (U : ℝ × ℂ → V 1)
    (hU : IsPageFamilyOn H J P γ y l I U) (a b : ℝ) (hab : Set.Icc a b ⊆ I)
    (K : Set (V 1)) (hK : IsCompact K) (hKP : Disjoint K (Set.range P.x)) :
    ∃ r : ℝ, ∀ t ∈ Set.Icc a b, ∀ z, pageMap H U (t, z) ∈ K → ‖z‖ ≤ r := by
  classical
  by_contra hcon
  push Not at hcon
  choose t₀ ht₀ z₀ hz₀K hz₀ using fun n : ℕ => hcon n
  have hne : ∀ p ∈ I ×ˢ (Set.univ : Set ℂ), U p ≠ 0 := fun p hp =>
    (hU.2 p.1 hp.1).1.1.1.2.1 p.2 trivial
  have hU1 : ContDiffOn ℝ 1 U (I ×ˢ Set.univ) := hU.1.of_le (by exact_mod_cast hl)
  have hO : IsOpen (I ×ˢ (Set.univ : Set ℂ)) := hI.prod isOpen_univ
  have hF := contDiffOn_pageMap H hH U I hI hU1 hne
  have hFS : ∀ p ∈ I ×ˢ (Set.univ : Set ℂ), pageMap H U p ∈ energySurface H := fun p hp =>
    (pfo_proj_mem hH (hne p hp))
  have hSc : IsClosed (energySurface H) := isClosed_eq hH.1.continuous continuous_const
  let K' := K ∩ energySurface H
  have hK' : IsCompact K' := hK.inter_right hSc
  have hK'0 : (0 : V 1) ∉ K' := fun h => pfo_ne_zero hH h.2 rfl
  have hK'P : ∀ q ∈ K', proj H q ∉ Set.range P.x := fun q hq h => by
    rw [pfo_proj_self hH hq.2] at h
    exact Set.disjoint_left.1 hKP hq.1 h
  have hmem : ∀ n, (t₀ n, pageMap H U (t₀ n, z₀ n)) ∈ Set.Icc a b ×ˢ K' := fun n =>
    ⟨ht₀ n, hz₀K n, hFS _ ⟨hab (ht₀ n), trivial⟩⟩
  obtain ⟨⟨tₗ, q⟩, ⟨htₗ, hq⟩, φ, hφ, hlim⟩ := (isCompact_Icc.prod hK').tendsto_subseq hmem
  have hpl : ∀ n, ∃ v ∈ embeddedFastPlaneSet H J P {pageMap H U (t₀ (φ n), z₀ (φ n))} γ,
      Set.range (fun z => proj H (v z)) = Set.range (fun z => proj H (U (t₀ (φ n), z))) := fun n =>
    have hm := hU.2 _ (hab (ht₀ (φ n)))
    exists_mem_embeddedFastPlaneSet_of_isEmbeddedPlane H hH J hJ P γ hγ hγT _ hm.1.1 hm.1.2.1 hm.2
      (z₀ (φ n))
  choose v₀ hv₀ hv₀r using hpl
  have hv₀K : ∀ n, v₀ n ∈ embeddedFastPlaneSet H J P K' γ := fun n =>
    ⟨⟨(hv₀ n).1.1, (hv₀ n).1.2.1, by rw [(hv₀ n).1.2.2.1]; exact (hmem (φ n)).2,
      (hv₀ n).1.2.2.2⟩, (hv₀ n).2⟩
  obtain ⟨ψ, hψ, w, hw, hvw⟩ := hΛ K' hK' hK'0 hK'P v₀ hv₀K
  -- the sequences
  let T : ℕ → ℝ := fun k => t₀ (φ (ψ k))
  let Z : ℕ → ℂ := fun k => z₀ (φ (ψ k))
  let v : ℕ → ℂ → V 1 := fun k => v₀ (ψ k)
  have hTI : ∀ k, T k ∈ I := fun k => hab (ht₀ _)
  have hlim' := hlim.comp hψ.tendsto_atTop
  have hT : Tendsto T atTop (𝓝 tₗ) := (continuous_fst.tendsto _).comp hlim'
  have hQ : Tendsto (fun k => pageMap H U (T k, Z k)) atTop (𝓝 q) :=
    (continuous_snd.tendsto _).comp hlim'
  have hZ : ∀ k : ℕ, (k : ℝ) < ‖Z k‖ := fun k => lt_of_le_of_lt
    (by exact_mod_cast (hψ.id_le k).trans (hφ.id_le _)) (hz₀ _)
  have htₗI : tₗ ∈ I := hab htₗ
  have hv0 : ∀ k, v k 0 = pageMap H U (T k, Z k) := fun k => (hv₀ (ψ k)).1.2.2.1
  -- the limit plane passes through `q`
  have hw0 : w 0 = q := by
    have h1 := (hvw {0} (Set.subset_univ _) isCompact_singleton 0).tendsto_at (Set.mem_singleton 0)
    have h2 : Tendsto (fun k => v k 0) atTop (𝓝 (w 0)) := by
      have h3 := ((ContinuousMultilinearMap.apply ℝ (fun _ : Fin 0 => ℂ) (V 1) 0).continuous.tendsto
        _).comp h1
      simpa [Function.comp_def] using h3
    simp only [hv0] at h2
    exact tendsto_nhds_unique h2 hQ
  obtain ⟨η, hη, hη0⟩ := exists_isReebTrajectory H hH q hq.2
  have hwη : w ∈ embeddedFastPlaneSet H J P {η 0} γ :=
    ⟨⟨hw.1.1, hw.1.2.1, by rw [hη0]; exact hw0, hw.1.2.2.2⟩, hw.2⟩
  obtain ⟨ε, hε, W, hW, hW0, -, -, hWv⟩ :=
    exists_local_page_family H hH J hJ P hcz γ η hη 0 w hwη l hl
  obtain ⟨A₁, B₁, r₁, s₀, -, -, -, hs₀, hev⟩ :=
    hWv v (fun k => ⟨(hv₀ _).1.1, (hv₀ _).1.2.1, (hv₀ _).2⟩) hvw
  -- make the times lie in the domain for all `k`
  let s : ℕ → ℝ := fun k => if s₀ k ∈ ball 0 ε then s₀ k else 0
  have hsB : ∀ k, s k ∈ ball (0 : ℝ) ε := fun k => by
    by_cases h : s₀ k ∈ ball 0 ε
    · simp only [s, h, if_true]
    · simp only [s, h, if_false]; exact mem_ball_self hε
  have hss : ∀ᶠ k in atTop, s k = s₀ k := by
    filter_upwards [hev] with k hk
    simp only [s, hk.1, if_true]
  have hs : Tendsto s atTop (𝓝 0) := hs₀.congr' (hss.mono fun k hk => hk.symm)
  have hmU := fun k => hU.2 _ (hTI k)
  have hmW := fun k => hW.2 _ (hsB k)
  have hWne : ∀ p ∈ ball (0 : ℝ) ε ×ˢ (Set.univ : Set ℂ), W p ≠ 0 := fun p hp =>
    (hW.2 p.1 hp.1).1.1.1.2.1 p.2 trivial
  have hW1 : ContDiffOn ℝ 1 W (ball (0 : ℝ) ε ×ˢ Set.univ) := hW.1.of_le (by exact_mod_cast hl)
  have hFW := contDiffOn_pageMap H hH W _ isOpen_ball hW1 hWne
  have hrel : ∀ᶠ k in atTop, ∃ (c : ℝ) (A B : ℂ), A ≠ 0 ∧
      ∀ z, U (T k, A * z + B) = Real.exp (2 * c) • W (s k, z) := by
    filter_upwards [hev, hss] with k hk hks
    have h1 := hk.2 0
    rw [← hks] at h1
    have h2 : proj H (W (s k, 0)) = proj H (v k (A₁ k * 0 + B₁ k)) := by
      rw [h1]
      exact (proj_aCoord_exp_smul H hH _ _ ((hv₀ _).1.1.1.2.1 _ trivial)).1
    have h3 := range_eq_of_proj_eq_of_mem_embeddedFastPlaneSet H hH J hJ P hcz γ γ _ _ _ _ (hmW k) (hv₀ (ψ k)) _ _ h2
    have h4 := (hv₀r (ψ k)).symm.trans h3.symm
    exact exists_shiftA_comp_affine_of_range_eq H hH J hJ P hcz _ _ (hmU k).1.1 (hmU k).1.2.1
      (hmU k).2 (hmW k).1.1 (hmW k).1.2.1 (hmW k).2 h4
  have hyS : ∀ t, proj H (y t) = y t := fun t => pfo_proj_self hH (hy.1 t)
  have hU0 : ∀ t ∈ I, pageMap H U (t, 0) = y t := fun t ht => by
    show proj H (U (t, 0)) = _
    rw [show U (t, 0) = y t from (hU.2 t ht).1.2.2.1, hyS]
  have hWη : ∀ t ∈ ball (0 : ℝ) ε, pageMap H W (t, 0) = η t := fun t ht => by
    show proj H (W (t, 0)) = _
    rw [show W (t, 0) = η t from (hW.2 t ht).1.2.2.1, pfo_proj_self hH (hη.1 t)]
  have hyc : Continuous y := continuous_iff_continuousAt.2 fun t => (hy.2 t).continuousAt
  have hηc : Continuous η := continuous_iff_continuousAt.2 fun t => (hη.2 t).continuousAt
  -- the energies
  have htot : ∀ u ∈ embeddedFastPlaneSet H J P Set.univ γ,
      dlambdaEnergy H Set.univ u = ENNReal.ofReal P.T := fun u hu =>
    dlambdaEnergy_univ_eq_of_isNondegenerateEnd H hH J hJ _ hu.1.1.1 P hu.1.2.1
  have hup : ∀ (K : Set (V 1)) u, u ∈ embeddedFastPlaneSet H J P K γ →
      u ∈ embeddedFastPlaneSet H J P Set.univ γ := fun K u hu =>
    ⟨⟨hu.1.1, hu.1.2.1, trivial, hu.1.2.2.2⟩, hu.2⟩
  have hhalf : ENNReal.ofReal (P.T / 2) + ENNReal.ofReal (P.T / 2) = ENNReal.ofReal P.T := by
    rw [← ENNReal.ofReal_add (by linarith [P.T_pos]) (by linarith [P.T_pos]), add_halves]
  have hlt2 : ENNReal.ofReal (P.T / 2) < ENNReal.ofReal P.T :=
    (ENNReal.ofReal_lt_ofReal_iff P.T_pos).2 (half_lt_self P.T_pos)
  obtain ⟨ρ₁, hρ₁0, hρ₁⟩ := exists_radius_lt_dlambdaEnergy_ball H (fun z => U (tₗ, z))
    (ENNReal.ofReal (P.T / 2)) (by rw [htot _ (hup _ _ (hU.2 tₗ htₗI))]; exact hlt2)
  obtain ⟨ρ₂, hρ₂0, hρ₂⟩ := exists_radius_lt_dlambdaEnergy_ball H (fun z => W (0, z))
    (ENNReal.ofReal (P.T / 2))
    (by rw [htot _ (hup _ _ (hW.2 0 (mem_ball_self hε)))]; exact hlt2)
  set ρ := max ρ₁ ρ₂ with hρdef
  have hρ0 : 0 ≤ ρ := hρ₁0.trans (le_max_left _ _)
  have hE1 := eventually_lt_dlambdaEnergy_slice H hH U I hI hU1 hne tₗ htₗI T hTI hT
    (ball 0 ρ₁) _ hρ₁
  have hE2 := eventually_lt_dlambdaEnergy_slice H hH W _ isOpen_ball hW1 hWne 0 (mem_ball_self hε)
    s hsB hs (ball 0 ρ₂) _ hρ₂
  have hmain : ∀ᶠ k in atTop, ∃ (c : ℝ) (A B : ℂ), A ≠ 0 ∧
      (∀ z, U (T k, A * z + B) = Real.exp (2 * c) • W (s k, z)) ∧ ‖B‖ < ρ + ‖A‖ * ρ := by
    filter_upwards [hrel, hE1, hE2] with k hk h1 h2
    obtain ⟨c, A, B, hA, hk⟩ := hk
    refine ⟨c, A, B, hA, hk, ?_⟩
    have hdw : Differentiable ℝ (fun w => proj H (U (T k, w))) := fun w =>
      (hF.contDiffAt (hO.mem_nhds ⟨hTI k, Set.mem_univ w⟩)).differentiableAt
        (by norm_num) |>.comp w ((differentiableAt_const _).prodMk differentiableAt_id)
    refine norm_lt_of_affine_of_dlambdaEnergy_lt H hH (fun w => U (T k, w)) (fun w => W (s k, w))
      c A B hA hdw (fun w => hWne _ ⟨hsB k, trivial⟩) hk ρ ?_
    rw [htot _ (hup _ _ (hmU k)), ← hhalf]
    exact ENNReal.add_lt_add
      (h1.trans_le (lintegral_mono_set (ball_subset_ball (le_max_left _ _))))
      (h2.trans_le (lintegral_mono_set (ball_subset_ball (le_max_right _ _))))
  -- in both cases `q` lies on the leaf at `tₗ`
  have hdich : ∀ᶠ k in atTop, (∃ B ∈ closedBall (0 : ℂ) (2 * ρ), pageMap H U (T k, B) = η (s k)) ∨
      ∃ D ∈ closedBall (0 : ℂ) (2 * ρ), pageMap H W (s k, D) = y (T k) := by
    filter_upwards [hmain] with k hk
    obtain ⟨c, A, B, hA, hk, hB⟩ := hk
    have hApos : 0 < ‖A‖ := norm_pos_iff.2 hA
    have hproj : ∀ z, pageMap H U (T k, A * z + B) = pageMap H W (s k, z) := fun z => by
      show proj H _ = proj H _
      rw [hk]
      exact (proj_aCoord_exp_smul H hH _ _ (hWne _ ⟨hsB k, trivial⟩)).1
    rcases le_total ‖A‖ 1 with h | h
    · refine Or.inl ⟨B, ?_, ?_⟩
      · rw [mem_closedBall, dist_zero_right]
        nlinarith
      · rw [← hWη _ (hsB k), ← hproj, mul_zero, zero_add]
    · refine Or.inr ⟨-B / A, ?_, ?_⟩
      · rw [mem_closedBall, dist_zero_right, norm_div, norm_neg, div_le_iff₀ hApos]
        nlinarith
      · rw [← hU0 _ (hTI k), ← hproj]
        congr 2
        field_simp
        ring
  have hfreq : (∃ᶠ k in atTop, ∃ B ∈ closedBall (0 : ℂ) (2 * ρ), pageMap H U (T k, B) = η (s k)) ∨
      ∃ᶠ k in atTop, ∃ D ∈ closedBall (0 : ℂ) (2 * ρ), pageMap H W (s k, D) = y (T k) :=
    Filter.frequently_or_distrib.1 hdich.frequently
  have hzs : ∃ z', pageMap H U (tₗ, z') = q := by
    rcases hfreq with h | h
    · obtain ⟨θ, hθ, hθB⟩ := extraction_of_frequently_atTop h
      choose B hB hBe using hθB
      obtain ⟨b', -, χ, hχ, hb'⟩ := (isCompact_closedBall (0 : ℂ) (2 * ρ)).tendsto_subseq hB
      have hm : Tendsto (fun k => θ (χ k)) atTop atTop := hθ.tendsto_atTop.comp hχ.tendsto_atTop
      refine ⟨b', ?_⟩
      have h1 : Tendsto (fun k => pageMap H U (T (θ (χ k)), B (χ k))) atTop
          (𝓝 (pageMap H U (tₗ, b'))) :=
        (hF.continuousOn.continuousAt (hO.mem_nhds ⟨htₗI, trivial⟩)).tendsto.comp
          ((hT.comp hm).prodMk_nhds hb')
      simp only [hBe] at h1
      rw [← hη0]
      exact tendsto_nhds_unique h1 ((hηc.tendsto 0).comp (hs.comp hm))
    · obtain ⟨θ, hθ, hθB⟩ := extraction_of_frequently_atTop h
      choose B hB hBe using hθB
      obtain ⟨b', -, χ, hχ, hb'⟩ := (isCompact_closedBall (0 : ℂ) (2 * ρ)).tendsto_subseq hB
      have hm : Tendsto (fun k => θ (χ k)) atTop atTop := hθ.tendsto_atTop.comp hχ.tendsto_atTop
      have h1 : Tendsto (fun k => pageMap H W (s (θ (χ k)), B (χ k))) atTop
          (𝓝 (pageMap H W (0, b'))) :=
        (hFW.continuousOn.continuousAt ((isOpen_ball.prod isOpen_univ).mem_nhds
          ⟨mem_ball_self hε, trivial⟩)).tendsto.comp ((hs.comp hm).prodMk_nhds hb')
      simp only [hBe] at h1
      have h2 := tendsto_nhds_unique h1 ((hyc.tendsto tₗ).comp (hT.comp hm))
      have h3 : proj H (W (0, b')) = proj H (U (tₗ, 0)) := h2.trans (hU0 _ htₗI).symm
      have h4 := range_eq_of_proj_eq_of_mem_embeddedFastPlaneSet H hH J hJ P hcz γ γ _ _ _ _
        (hW.2 0 (mem_ball_self hε)) (hU.2 _ htₗI) _ _ h3
      have h5 : q ∈ Set.range (fun z => proj H (W (0, z))) :=
        ⟨0, (hWη 0 (mem_ball_self hε)).trans hη0⟩
      rw [h4] at h5
      exact h5
  obtain ⟨z', hz'⟩ := hzs
  obtain ⟨ε₀, hε₀, hε₀I, hε₀i⟩ :=
    injOn_pageMap_of_isPageFamilyOn H hH J hJ P hcz γ y hy l hl I hI U hU tₗ htₗI
  have hopen := nhdsWithin_energySurface_le_map (by simp [Module.finrank_prod]) H hH
    (pageMap H U) (tₗ, z') (hF.contDiffAt (hO.mem_nhds ⟨htₗI, trivial⟩))
    (by filter_upwards [hO.mem_nhds (show (tₗ, z') ∈ I ×ˢ (Set.univ : Set ℂ) from
          ⟨htₗI, trivial⟩)] with p hp using hFS p hp)
    (injective_fderiv_pageMap_of_isPageFamilyOn H hH J hJ P hcz γ y hy l hl I hI U hU tₗ htₗI z')
  have hN : pageMap H U '' (ball tₗ ε₀ ×ˢ ball z' 1) ∈ 𝓝[energySurface H] (pageMap H U (tₗ, z')) :=
    hopen (image_mem_map (prod_mem_nhds (ball_mem_nhds _ hε₀) (ball_mem_nhds _ one_pos)))
  rw [hz'] at hN
  have hQ' : Tendsto (fun k => pageMap H U (T k, Z k)) atTop (𝓝[energySurface H] q) :=
    tendsto_nhdsWithin_iff.2 ⟨hQ, Eventually.of_forall fun k => hFS _ ⟨hTI k, trivial⟩⟩
  obtain ⟨k, ⟨⟨⟨p₁, p₂⟩, ⟨hp₁, hp₂⟩, hp⟩, hkT⟩, hk⟩ := ((hQ'.eventually hN).and
    (hT.eventually (ball_mem_nhds _ hε₀)) |>.and
    (eventually_ge_atTop ⌈‖z'‖ + 1⌉₊)).exists
  have heq := hε₀i
    (show (p₁, p₂) ∈ ball tₗ ε₀ ×ˢ Set.univ from ⟨hp₁, trivial⟩)
    (show (T k, Z k) ∈ ball tₗ ε₀ ×ˢ Set.univ from ⟨mem_ball.2 hkT, trivial⟩) hp
  have h1 : p₂ = Z k := congrArg Prod.snd heq
  have h2 : ‖Z k‖ < ‖z'‖ + 1 := by
    rw [← h1]
    have h3 : ‖p₂ - z'‖ < 1 := by rw [← dist_eq_norm]; exact hp₂
    have := norm_le_insert' p₂ z'
    linarith
  have h3 : ‖z'‖ + 1 ≤ k := (Nat.le_ceil _).trans (by exact_mod_cast hk)
  linarith [hZ k]

end FiniteEnergyPlane

open FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem solution (H : V 1 → ℝ)
    (hH : IsStrictlyStarShapedLevel H)
    (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J)
    (P : ReebOrbit H) (hcz : P.IsCZAtLeast 3) (γ : ℝ) (hγ : 0 < γ) (hγT : γ < P.T)
    (hΛ : ∀ K : Set (V 1), IsCompact K → (0 : V 1) ∉ K → (∀ y ∈ K, proj H y ∉ Set.range P.x) →
      IsSeqCompactCInftyLoc (embeddedFastPlaneSet H J P K γ))
    (y : ℝ → V 1) (hy : IsReebTrajectory H y)
    (l : ℕ) (hl : 1 ≤ l) (I : Set ℝ) (hI : IsOpen I) (U : ℝ × ℂ → V 1)
    (hU : IsPageFamilyOn H J P γ y l I U) (a b : ℝ) (hab : Set.Icc a b ⊆ I)
    (K : Set (V 1)) (hK : IsCompact K) (hKP : Disjoint K (Set.range P.x)) :
    ∃ r : ℝ, ∀ t ∈ Set.Icc a b, ∀ z, pageMap H U (t, z) ∈ K → ‖z‖ ≤ r :=
  exists_norm_le_of_pageMap_mem_aux H hH J hJ P hcz γ hγ hγT hΛ y hy l hl I hI U hU a b hab K hK hKP
