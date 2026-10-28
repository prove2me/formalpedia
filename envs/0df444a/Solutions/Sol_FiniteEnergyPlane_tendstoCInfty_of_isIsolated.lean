-- Prove2me | solution 1 for FiniteEnergyPlane.tendstoCInfty_of_isIsolated
-- status  : ACCEPTED   (prove)
-- author  : @Alien60
-- created : 2026-10-25T23:17:46.295879+00:00
-- url     : https://prove2.me/submissions/c12d20e6-82f6-45dd-a20f-225f3562d1a6

import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Add
import Definitions.Def_FiniteEnergyPlane_Setting
import Theorems.Thm_FiniteEnergyPlane_reeb_spec
import Theorems.Thm_FiniteEnergyPlane_punctured_disk_asymptotics
import Theorems.Thm_FiniteEnergyPlane_continuousOn_proj
import Theorems.Thm_FiniteEnergyPlane_eventually_norm_sub_comp_cwLoop_le
import Theorems.Thm_FiniteEnergyPlane_ReebOrbit_apply_eq_apply_add_of_apply_eq

open FiniteEnergyPlane MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- Wendl, Lemma 9.18, as a reduction to Wendl's Theorem 9.8 (`punctured_disk_asymptotics`),
`reeb_spec`, continuity of `proj`, continuity of circle loops in the radius, and uniqueness of
Reeb trajectories. -/
theorem solution {n : ℕ} (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V n → V n →L[ℝ] V n) (hJ : IsCompatibleXiStructure H J) (u : ℂ → V n)
    (hu : IsFiniteEnergyCurve H J (ball 0 1 \ {0}) u) (hnr : ¬ IsRemovablePuncture H J u 0 1)
    (P : ReebOrbit H) (hP : P.IsIsolated) (σ : ℝ) (hσ : σ = 1 ∨ σ = -1)
    (ρ : ℕ → ℝ) (hρ : ∀ k, 0 < ρ k) (hρ0 : Tendsto ρ atTop (𝓝 0)) (c : ℝ)
    (hconv : TendstoCInfty (fun k => loopInS H u (cwLoop 0 (ρ k)))
      (fun t => P.x (σ * P.T * t + c))) :
    ∀ m : ℕ, ∀ ε : ℝ, 0 < ε → ∀ᶠ r in 𝓝[>] (0 : ℝ), ∃ c' : ℝ, ∀ j ≤ m, ∀ t : ℝ,
      ‖iteratedDeriv j (loopInS H u (cwLoop 0 r)) t -
        iteratedDeriv j (fun t => P.x (σ * P.T * t + c')) t‖ ≤ ε := by
  intro m ε hε
  set L : ℝ → ℝ → V n := fun r => loopInS H u (cwLoop 0 r) with hL
  have hPT := P.T_pos
  -- Step 0: Wendl, Theorem 9.8 (subsequential convergence to orbits of charge `Q₀`).
  rcases punctured_disk_asymptotics H hH J hJ u hu with hrem | ⟨Q₀, -, -, -, -, hsub⟩
  · exact absurd hrem hnr
  have hderiv : ∀ (R : ReebOrbit H) (a b t : ℝ),
      HasDerivAt (fun t => R.x (a * t + b)) (a • reeb H (R.x (a * t + b))) t := by
    intro R a b t
    have h1 : HasDerivAt (fun t => a * t + b) a t := by
      simpa using ((hasDerivAt_id t).const_mul a).add_const b
    exact (R.hasDerivAt (a * t + b)).scomp t h1
  have hlin : ∀ (y : V n) (a : ℝ) (v : V n), liouville y (a • v) = a * liouville y v := by
    intro y a v
    simp only [liouville, omega0, dot, Pi.smul_apply, smul_eq_mul]
    rw [mul_div_assoc', Finset.mul_sum]
    congr 1
    exact Finset.sum_congr rfl fun i _ => by ring
  -- The charge is `σ T`: compare the derivatives of the two limits of the loops along `ρ`.
  have hQ : Q₀ = σ * P.T := by
    obtain ⟨φ, hφ, P₀, -, c₀, hc₀⟩ := hsub ρ hρ hρ0
    have h0 : P.x (σ * P.T * 0 + c) = P₀.x (Q₀ * 0 + c₀) := by
      have e1 := ((hconv 0).tendsto_at 0).comp hφ.tendsto_atTop
      have e2 := (hc₀ 0).tendsto_at 0
      simp only [iteratedDeriv_zero] at e1 e2
      exact tendsto_nhds_unique e1 e2
    have h1 : deriv (fun t => P.x (σ * P.T * t + c)) 0 =
        deriv (fun t => P₀.x (Q₀ * t + c₀)) 0 := by
      have e1 := ((hconv 1).tendsto_at 0).comp hφ.tendsto_atTop
      have e2 := (hc₀ 1).tendsto_at 0
      simp only [iteratedDeriv_one] at e1 e2
      exact tendsto_nhds_unique e1 e2
    rw [(hderiv P _ _ 0).deriv, (hderiv P₀ _ _ 0).deriv, ← h0] at h1
    have hl := congrArg (liouville (P.x (σ * P.T * 0 + c))) h1
    have hR := (reeb_spec H hH _ (P.mem (σ * P.T * 0 + c))).2.1
    rw [hlin, hlin, hR] at hl
    linarith
  have hPTabs : |Q₀| = P.T := by
    rw [hQ, abs_mul]; rcases hσ with rfl | rfl <;> simp [abs_of_pos hPT]
  -- Step 1: every sequence of radii has a subsequence converging to a `T`-periodic orbit
  -- traversed with the same speed `σ T`.
  have hsub' : ∀ r : ℕ → ℝ, (∀ k, 0 < r k) → Tendsto r atTop (𝓝 0) →
      ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ ∃ Q : ReebOrbit H, Q.T = P.T ∧ ∃ c' : ℝ,
        TendstoCInfty (fun k => L (r (ψ k))) (fun t => Q.x (σ * P.T * t + c')) := by
    intro r hr hr0
    obtain ⟨ψ, hψ, Q, hQT, c', hc'⟩ := hsub r hr hr0
    refine ⟨ψ, hψ, Q, hQT.trans hPTabs, c', ?_⟩
    rw [← hQ]; exact hc'
  -- Isolation: a `T`-orbit passing within `δ` of `x(ℝ)` has its image in `x(ℝ)`.
  obtain ⟨W, hWo, hPW, hW⟩ := hP
  have hPcont : Continuous P.x :=
    continuous_iff_continuousAt.2 fun τ => (P.hasDerivAt τ).continuousAt
  set Rg := Set.range P.x with hRg
  have hRgc : IsCompact Rg :=
    (show Function.Periodic P.x P.T from P.periodic).compact_of_continuous hPT.ne' hPcont
  obtain ⟨δ, hδ, hthick⟩ := hRgc.exists_thickening_subset_open hWo hPW
  have hiso : ∀ Q : ReebOrbit H, Q.T = P.T → ∀ τ, infDist (Q.x τ) Rg < δ →
      Set.range Q.x ⊆ Rg := fun Q hQT τ h =>
    hW Q hQT ⟨τ, hthick ((mem_thickening_iff_infDist_lt (Set.range_nonempty P.x)).2 h)⟩
  -- `g r` measures how far the loop of radius `r` leaves `x(ℝ)` (capped at `1`).
  set g : ℝ → ℝ := fun r => ⨆ t : ℝ, min (infDist (L r t) Rg) 1 with hg
  have hgbdd : ∀ r, BddAbove (Set.range fun t => min (infDist (L r t) Rg) 1) :=
    fun r => ⟨1, by rintro _ ⟨t, rfl⟩; exact min_le_right _ _⟩
  have hle_g : ∀ r t, min (infDist (L r t) Rg) 1 ≤ g r := fun r t => le_ciSup (hgbdd r) t
  have hg_le : ∀ r b, (∀ t, min (infDist (L r t) Rg) 1 ≤ b) → g r ≤ b :=
    fun r b h => ciSup_le h
  have hF : ContinuousOn (fun z => proj H (u z)) (ball (0 : ℂ) 1 \ {0}) :=
    (continuousOn_proj H hH).comp hu.1.continuousOn (fun z hz => hu.2.1 z hz)
  have hgcont : ContinuousOn g (Set.Ioo 0 1) := by
    intro r₀ hr₀
    refine (Metric.tendsto_nhds.2 fun e he => ?_).mono_left nhdsWithin_le_nhds
    have key : ∀ r' r'' : ℝ, (∀ t, ‖L r' t - L r'' t‖ ≤ e / 2) → g r' ≤ g r'' + e / 2 := by
      intro r' r'' h
      apply hg_le
      intro t
      have h1 : infDist (L r' t) Rg ≤ infDist (L r'' t) Rg + e / 2 := by
        have := infDist_le_infDist_add_dist (x := L r' t) (y := L r'' t) (s := Rg)
        rw [dist_eq_norm] at this
        linarith [h t]
      have h2 : min (infDist (L r' t) Rg) 1 ≤ min (infDist (L r'' t) Rg) 1 + e / 2 := by
        rcases le_total (infDist (L r'' t) Rg) 1 with h3 | h3
        · rw [min_eq_left h3]; exact (min_le_left _ _).trans h1
        · rw [min_eq_right h3]; linarith [min_le_right (infDist (L r' t) Rg) 1]
      linarith [hle_g r'' t]
    filter_upwards [eventually_norm_sub_comp_cwLoop_le _ 0 1 hF r₀ hr₀ (e / 2) (half_pos he)]
      with r hr
    have hr' : ∀ t, ‖L r t - L r₀ t‖ ≤ e / 2 := hr
    have hr'' : ∀ t, ‖L r₀ t - L r t‖ ≤ e / 2 := fun t => by rw [norm_sub_rev]; exact hr' t
    have k1 := key r r₀ hr'
    have k2 := key r₀ r hr''
    rw [Real.dist_eq, abs_sub_lt_iff]
    constructor <;> linarith
  set η := min (δ / 2) (1 / 2) with hη
  have hη0 : 0 < η := lt_min (half_pos hδ) one_half_pos
  have hη1 : η < 1 := (min_le_right _ _).trans_lt one_half_lt_one
  have hηδ : η ≤ δ / 2 := min_le_left _ _
  -- A limit orbit of loops with `g ≤ η` has its image in `x(ℝ)`.
  have hnear : ∀ (r : ℝ) (Q : ReebOrbit H) (c' : ℝ), Q.T = P.T → g r ≤ η →
      (∀ t, dist (Q.x (σ * P.T * t + c')) (L r t) < η / 4) → Set.range Q.x ⊆ Rg := by
    intro r Q c' hQT hgr hd
    apply hiso Q hQT (σ * P.T * 0 + c')
    have h1 : infDist (L r 0) Rg ≤ η :=
      (min_le_iff.1 ((hle_g r 0).trans hgr)).resolve_right (not_le.2 hη1)
    have h2 := infDist_le_infDist_add_dist (x := Q.x (σ * P.T * 0 + c')) (y := L r 0) (s := Rg)
    have h3 := hd 0
    linarith
  have hρg : ∀ᶠ k in atTop, g (ρ k) < η := by
    have h0 := hconv 0
    simp only [iteratedDeriv_zero] at h0
    filter_upwards [Metric.tendstoUniformly_iff.1 h0 (η / 2) (half_pos hη0)] with k hk
    refine lt_of_le_of_lt (hg_le _ (η / 2) fun t => ?_) (half_lt_self hη0)
    refine (min_le_left _ _).trans ?_
    calc infDist (L (ρ k) t) Rg ≤ dist (L (ρ k) t) (P.x (σ * P.T * t + c)) :=
          infDist_le_dist_of_mem ⟨_, rfl⟩
      _ ≤ η / 2 := by rw [dist_comm]; exact (hk t).le
  have hrad : ∀ k : ℕ, (0 : ℝ) < 1 / ((k : ℝ) + 1) ∧ 1 / ((k : ℝ) + 1) ≤ 1 := fun k => by
    refine ⟨by positivity, ?_⟩
    rw [div_le_one (by positivity)]
    linarith [k.cast_nonneg (α := ℝ)]
  have hseq0 : ∀ r : ℕ → ℝ, (∀ k : ℕ, r k ∈ Set.Ioo 0 (1 / ((k : ℝ) + 1))) →
      Tendsto r atTop (𝓝 0) := fun r hr =>
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      tendsto_one_div_add_atTop_nhds_zero_nat (fun k => (hr k).1.le) (fun k => (hr k).2.le)
  -- Step 2 (connectedness): eventually `g r ≤ η`.
  have hA : ∀ᶠ r in 𝓝[>] (0 : ℝ), g r ≤ η := by
    by_contra hcon
    rw [Filter.not_eventually] at hcon
    have hseq : ∀ k : ℕ, ∃ r, r ∈ Set.Ioo 0 (1 / ((k : ℝ) + 1)) ∧ g r = η := by
      intro k
      obtain ⟨hk, hk1⟩ := hrad k
      obtain ⟨b, hgb, hb⟩ := (hcon.and_eventually (Ioo_mem_nhdsGT hk)).exists
      obtain ⟨j, hj1, hj2⟩ := (hρg.and (hρ0.eventually (gt_mem_nhds hk))).exists
      have hab : Set.uIcc (ρ j) b ⊆ Set.Ioo 0 (1 / ((k : ℝ) + 1)) :=
        Set.ordConnected_Ioo.uIcc_subset ⟨hρ j, hj2⟩ hb
      have hc := hgcont.mono (hab.trans (Set.Ioo_subset_Ioo_right hk1))
      obtain ⟨r, hr, hgr⟩ :=
        intermediate_value_uIcc hc (Set.mem_uIcc.2 (Or.inl ⟨hj1.le, (not_le.1 hgb).le⟩))
      exact ⟨r, hab hr, hgr⟩
    choose r' hr' hgr' using hseq
    obtain ⟨ψ, hψ, Q, hQT, c', hc'⟩ := hsub' r' (fun k => (hr' k).1) (hseq0 r' hr')
    have h0 := hc' 0
    simp only [iteratedDeriv_zero] at h0
    obtain ⟨k, hk⟩ := (Metric.tendstoUniformly_iff.1 h0 (η / 4) (by positivity)).exists
    have hlt : η / 2 < ⨆ t : ℝ, min (infDist (L (r' (ψ k)) t) Rg) 1 := by
      change η / 2 < g (r' (ψ k))
      rw [hgr' (ψ k)]; linarith
    obtain ⟨t₀, ht₀⟩ := exists_lt_of_lt_ciSup hlt
    have hRsub := hnear _ Q c' hQT (hgr' (ψ k)).le hk
    have hz : infDist (Q.x (σ * P.T * t₀ + c')) Rg = 0 := infDist_zero_of_mem (hRsub ⟨_, rfl⟩)
    have h2 := infDist_le_infDist_add_dist (x := L (r' (ψ k)) t₀)
      (y := Q.x (σ * P.T * t₀ + c')) (s := Rg)
    have h3 := hk t₀
    rw [dist_comm] at h3
    linarith [(lt_min_iff.1 ht₀).1]
  -- Step 3: limits along small radii are reparametrizations of `P`; conclude by contradiction.
  by_contra hcon
  rw [Filter.not_eventually] at hcon
  have hseq : ∀ k : ℕ, ∃ r, r ∈ Set.Ioo 0 (1 / ((k : ℝ) + 1)) ∧ g r ≤ η ∧
      ¬ ∃ c' : ℝ, ∀ j ≤ m, ∀ t : ℝ, ‖iteratedDeriv j (L r) t -
        iteratedDeriv j (fun t => P.x (σ * P.T * t + c')) t‖ ≤ ε := by
    intro k
    obtain ⟨r, ⟨hr1, hr2⟩, hr3⟩ :=
      ((hcon.and_eventually hA).and_eventually (Ioo_mem_nhdsGT (hrad k).1)).exists
    exact ⟨r, hr3, hr2, hr1⟩
  choose r' hr' hgr' hbad using hseq
  obtain ⟨ψ, hψ, Q, hQT, c', hc'⟩ := hsub' r' (fun k => (hr' k).1) (hseq0 r' hr')
  have h0 := hc' 0
  simp only [iteratedDeriv_zero] at h0
  obtain ⟨k₀, hk₀⟩ := (Metric.tendstoUniformly_iff.1 h0 (η / 4) (by positivity)).exists
  obtain ⟨τ₂, hτ₂⟩ := hnear _ Q c' hQT (hgr' (ψ k₀)) hk₀ ⟨c', rfl⟩
  have shift := ReebOrbit.apply_eq_apply_add_of_apply_eq hH P Q hτ₂.symm
  have hfun : (fun t => Q.x (σ * P.T * t + c')) = fun t => P.x (σ * P.T * t + τ₂) := by
    funext t; rw [shift]; congr 1; ring
  rw [hfun] at hc'
  have hev : ∀ᶠ k in atTop, ∀ j ∈ Finset.range (m + 1), ∀ t,
      dist (iteratedDeriv j (fun t => P.x (σ * P.T * t + τ₂)) t)
        (iteratedDeriv j (L (r' (ψ k))) t) < ε :=
    (Filter.eventually_all_finset _).2 fun j _ => Metric.tendstoUniformly_iff.1 (hc' j) ε hε
  obtain ⟨k, hk⟩ := hev.exists
  refine hbad (ψ k) ⟨τ₂, fun j hj t => ?_⟩
  have := hk j (Finset.mem_range.2 (Nat.lt_succ_of_le hj)) t
  rw [dist_comm, dist_eq_norm] at this
  exact this.le

