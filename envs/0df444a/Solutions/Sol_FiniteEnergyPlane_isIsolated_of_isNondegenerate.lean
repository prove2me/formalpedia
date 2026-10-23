-- Prove2me | solution 1 for FiniteEnergyPlane.isIsolated_of_isNondegenerate
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T06:57:31.161906+00:00
-- url     : https://prove2.me/submissions/16c30c56-a849-4c75-a193-d0be2db8e311

import Mathlib
import Definitions.Def_FiniteEnergyPlane_Asymptotics
import Theorems.Thm_FiniteEnergyPlane_reeb_spec
import Theorems.Thm_FiniteEnergyPlane_linReebFlow_spec

set_option linter.all false

open Set Metric Filter Topology

namespace IsoCore

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Gronwall with bootstrap: trajectories starting close stay close, as long as the
predicted bound stays below the radius of the Lipschitz tubes. -/
lemma traj_close {R : E → E} {x Q : ℝ → E} {K : NNReal} {δ : ℝ}
    (hL : ∀ t, LipschitzOnWith K R (ball (x t) δ))
    (hx : ∀ t, HasDerivAt x (R (x t)) t) (hQ : ∀ t, HasDerivAt Q (R (Q t)) t)
    {a b ε : ℝ} (h0 : dist (Q a) (x a) ≤ ε) (hε : ε * Real.exp (K * (b - a)) < δ) :
    ∀ t ∈ Icc a b, dist (Q t) (x t) ≤ ε * Real.exp (K * (t - a)) := by
  have hxc : Continuous x := continuous_iff_continuousAt.2 fun t => (hx t).continuousAt
  have hQc : Continuous Q := continuous_iff_continuousAt.2 fun t => (hQ t).continuousAt
  have gron : ∀ c ∈ Icc a b, (∀ t ∈ Ico a c, dist (Q t) (x t) < δ) →
      ∀ t ∈ Icc a c, dist (Q t) (x t) ≤ ε * Real.exp (K * (t - a)) := by
    intro c hc hin
    have hδ : 0 < δ := lt_of_le_of_lt (le_trans dist_nonneg h0 |> fun h =>
      mul_nonneg h (Real.exp_pos _).le) hε
    exact dist_le_of_trajectories_ODE_of_mem (v := fun _ => R) (s := fun t => ball (x t) δ)
      (fun t _ => hL t) hQc.continuousOn (fun t _ => (hQ t).hasDerivWithinAt)
      (fun t ht => mem_ball.2 (hin t ht)) hxc.continuousOn (fun t _ => (hx t).hasDerivWithinAt)
      (fun t _ => mem_ball_self hδ) h0
  have mono : ∀ t ∈ Icc a b, ε * Real.exp (K * (t - a)) < δ := by
    intro t ht
    refine lt_of_le_of_lt ?_ hε
    have hε0 : 0 ≤ ε := le_trans dist_nonneg h0
    gcongr
    exact ht.2
  -- the set of bad times
  by_cases hS : ∃ t ∈ Icc a b, δ ≤ dist (Q t) (x t)
  · exfalso
    set S := Icc a b ∩ {t | δ ≤ dist (Q t) (x t)} with hSdef
    have hSc : IsClosed S := isClosed_Icc.inter (isClosed_le continuous_const (hQc.dist hxc))
    have hSne : S.Nonempty := by obtain ⟨t, ht, h⟩ := hS; exact ⟨t, ht, h⟩
    have hSb : BddBelow S := ⟨a, fun t ht => ht.1.1⟩
    have hmem := hSc.csInf_mem hSne hSb
    set c := sInf S
    have hc : c ∈ Icc a b := hmem.1
    have hin : ∀ t ∈ Ico a c, dist (Q t) (x t) < δ := by
      intro t ht
      by_contra hcon
      push Not at hcon
      have : c ≤ t := csInf_le hSb ⟨⟨ht.1, ht.2.le.trans hc.2⟩, hcon⟩
      exact absurd ht.2 (not_lt.2 this)
    have := gron c hc hin c ⟨hc.1, le_rfl⟩
    have h2 := mono c hc
    exact absurd hmem.2 (not_le.2 (lt_of_le_of_lt this h2))
  · push Not at hS
    intro t ht
    exact gron b ⟨ht.1.trans ht.2, le_rfl⟩ (fun t ht => hS t ⟨ht.1, ht.2.le⟩) t ht


variable [FiniteDimensional ℝ E]

lemma range_compact {x : ℝ → E} {T : ℝ} (hT : 0 < T) (hxc : Continuous x)
    (hper : ∀ t, x (t + T) = x t) : IsCompact (range x) := by
  have : range x = x '' Icc 0 T := by
    apply subset_antisymm
    · rintro _ ⟨t, rfl⟩
      obtain ⟨y, hy, hxy⟩ := Function.Periodic.exists_mem_Ico₀ (c := T) (f := x) hper hT t
      exact ⟨y, Ico_subset_Icc_self hy, hxy.symm⟩
    · exact image_subset_range _ _
  rw [this]; exact isCompact_Icc.image hxc

lemma setup {R : E → E} {U : Set E} (hU : IsOpen U) (hR : ContDiffOn ℝ 1 R U)
    {x : ℝ → E} {T : ℝ} (hT : 0 < T) (hxc : Continuous x) (hper : ∀ t, x (t + T) = x t)
    (hxU : ∀ t, x t ∈ U) :
    ∃ δ > 0, ∃ K : NNReal, 0 < (K : ℝ) ∧ (∀ t, LipschitzOnWith K R (ball (x t) δ)) ∧
      (∀ t, ‖fderiv ℝ R (x t)‖ ≤ K) ∧
      (∀ η > 0, ∃ r > 0, r ≤ δ ∧ ∀ τ y, dist y (x τ) < r →
        ‖R y - R (x τ) - fderiv ℝ R (x τ) (y - x τ)‖ ≤ η * ‖y - x τ‖) := by
  have hcpt := range_compact hT hxc hper
  obtain ⟨δ, hδ, hsub⟩ := hcpt.exists_cthickening_subset_open hU (by rintro _ ⟨t, rfl⟩; exact hxU t)
  have hK0 : IsCompact (cthickening δ (range x)) := hcpt.cthickening
  have hdiff : ∀ y ∈ U, DifferentiableAt ℝ R y := fun y hy =>
    (hR.differentiableOn one_ne_zero y hy).differentiableAt (hU.mem_nhds hy)
  have hcont : ContinuousOn (fderiv ℝ R) U := hR.continuousOn_fderiv_of_isOpen hU le_rfl
  obtain ⟨M, hM⟩ := hK0.exists_bound_of_continuousOn (hcont.mono hsub)
  have hball : ∀ t, ball (x t) δ ⊆ cthickening δ (range x) := fun t =>
    (ball_subset_thickening (mem_range_self t) δ).trans (thickening_subset_cthickening _ _)
  set K : NNReal := Real.toNNReal (M + 1) with hKdef
  have hKM : (M : ℝ) + 1 ≤ K := Real.le_coe_toNNReal _
  have hMK : ∀ y ∈ cthickening δ (range x), ‖fderiv ℝ R y‖ ≤ K := fun y hy =>
    (hM y hy).trans (by linarith)
  refine ⟨δ, hδ, K, ?_, ?_, ?_, ?_⟩
  · have : 0 ≤ M := (norm_nonneg _).trans (hM _ (self_subset_cthickening _ (mem_range_self 0)))
    linarith
  · intro t
    apply (convex_ball (x t) δ).lipschitzOnWith_of_nnnorm_fderiv_le (𝕜 := ℝ)
    · exact fun y hy => hdiff y (hsub (hball t hy))
    · intro y hy
      have := hMK y (hball t hy)
      exact_mod_cast this
  · exact fun t => hMK _ (self_subset_cthickening _ (mem_range_self t))
  · intro η hη
    have huc := hK0.uniformContinuousOn_of_continuous (hcont.mono hsub)
    rw [Metric.uniformContinuousOn_iff] at huc
    obtain ⟨ρ, hρ, hρ'⟩ := huc η hη
    refine ⟨min ρ δ, lt_min hρ hδ, min_le_right _ _, ?_⟩
    intro τ y hy
    have hyb : ∀ z ∈ ball (x τ) (min ρ δ), z ∈ cthickening δ (range x) := fun z hz =>
      hball τ (ball_subset_ball (min_le_right _ _) hz)
    have key := (convex_ball (x τ) (min ρ δ)).norm_image_sub_le_of_norm_fderiv_le
      (𝕜 := ℝ) (f := fun z => R z - fderiv ℝ R (x τ) z) (C := η) (x := x τ) (y := y)
      (fun z hz => ((hdiff z (hsub (hyb z hz))).sub (fderiv ℝ R (x τ)).differentiableAt))
      (fun z hz => by
        rw [fderiv_fun_sub (hdiff z (hsub (hyb z hz))) (fderiv ℝ R (x τ)).differentiableAt,
          ContinuousLinearMap.fderiv]
        have := hρ' z (hyb z hz) (x τ) (hyb _ (mem_ball_self (lt_min hρ hδ)))
          (lt_of_lt_of_le (mem_ball.1 hz) (min_le_left _ _))
        rw [dist_eq_norm] at this
        exact this.le)
      (mem_ball_self (lt_min hρ hδ)) (mem_ball.2 hy)
    simpa [map_sub, sub_sub, sub_add_eq_sub_sub, add_comm, add_left_comm, add_assoc,
      sub_eq_add_neg] using key

lemma deriv_est {R : E → E} {x : ℝ → E} {Φ : ℝ → E →L[ℝ] E} {T δ : ℝ} {K : NNReal}
    (hT : 0 ≤ T) (hK : 0 < (K : ℝ))
    (hL : ∀ t, LipschitzOnWith K R (ball (x t) δ)) (hA : ∀ t, ‖fderiv ℝ R (x t)‖ ≤ K)
    (hrem : ∀ η > 0, ∃ r > 0, r ≤ δ ∧ ∀ τ y, dist y (x τ) < r →
        ‖R y - R (x τ) - fderiv ℝ R (x τ) (y - x τ)‖ ≤ η * ‖y - x τ‖)
    (hx : ∀ t, HasDerivAt x (R (x t)) t)
    (hΦ0 : Φ 0 = ContinuousLinearMap.id ℝ E)
    (hΦ : ∀ t, HasDerivAt Φ ((fderiv ℝ R (x t)).comp (Φ t)) t) :
    ∀ η > 0, ∃ r > 0, ∀ Q : ℝ → E, (∀ t, HasDerivAt Q (R (Q t)) t) →
      dist (Q 0) (x 0) < r → ‖Q T - x T - Φ T (Q 0 - x 0)‖ ≤ η * ‖Q 0 - x 0‖ := by
  intro η hη
  set C := Real.exp (K * T) with hC
  have hCpos : 0 < C := Real.exp_pos _
  have hCB : 0 < C * (C / K) := mul_pos hCpos (div_pos hCpos hK)
  obtain ⟨r', hr', hr'δ, hrem'⟩ := hrem (η / (C * (C / K))) (div_pos hη hCB)
  refine ⟨r' / C, div_pos hr' hCpos, ?_⟩
  intro Q hQ hd
  set v := Q 0 - x 0 with hv
  have hdv : dist (Q 0) (x 0) = ‖v‖ := dist_eq_norm _ _
  have hvC : ‖v‖ * C < r' := by rw [← hdv]; exact (lt_div_iff₀ hCpos).1 hd
  have hclose := traj_close hL hx hQ (a := 0) (b := T) (ε := ‖v‖) hdv.le
    (by rw [sub_zero]; exact lt_of_lt_of_le hvC hr'δ)
  have hclose' : ∀ t ∈ Icc 0 T, ‖Q t - x t‖ ≤ ‖v‖ * C := by
    intro t ht
    rw [← dist_eq_norm]
    refine (hclose t ht).trans ?_
    have : 0 ≤ ‖v‖ := norm_nonneg _
    rw [hC, sub_zero]
    gcongr
    exact ht.2
  set ε := η / (C * (C / K)) * (‖v‖ * C) with hε
  set e : ℝ → E := fun t => Q t - x t - Φ t v with he
  have he' : ∀ t, HasDerivAt e (R (Q t) - R (x t) - ((fderiv ℝ R (x t)).comp (Φ t)) v) t := by
    intro t
    exact ((hQ t).sub (hx t)).sub ((hΦ t).clm_apply (hasDerivAt_const t v) |>.congr_deriv
      (by simp))
  have hcont : Continuous e := continuous_iff_continuousAt.2 fun t => (he' t).continuousAt
  have hbound : ∀ t ∈ Ico 0 T,
      ‖R (Q t) - R (x t) - ((fderiv ℝ R (x t)).comp (Φ t)) v‖ ≤ K * ‖e t‖ + ε := by
    intro t ht
    have hsplit : R (Q t) - R (x t) - ((fderiv ℝ R (x t)).comp (Φ t)) v =
        (R (Q t) - R (x t) - fderiv ℝ R (x t) (Q t - x t)) + fderiv ℝ R (x t) (e t) := by
      simp only [he, map_sub, ContinuousLinearMap.comp_apply]; abel
    rw [hsplit]
    have h1 : ‖R (Q t) - R (x t) - fderiv ℝ R (x t) (Q t - x t)‖ ≤ ε := by
      have hq := hclose' t (Ico_subset_Icc_self ht)
      refine (hrem' t (Q t) (by rw [dist_eq_norm]; exact lt_of_le_of_lt hq hvC)).trans ?_
      rw [hε]
      exact mul_le_mul_of_nonneg_left hq (div_pos hη hCB).le
    have h2 : ‖fderiv ℝ R (x t) (e t)‖ ≤ K * ‖e t‖ :=
      ((fderiv ℝ R (x t)).le_opNorm _).trans (mul_le_mul_of_nonneg_right (hA t) (norm_nonneg _))
    calc _ ≤ ‖R (Q t) - R (x t) - fderiv ℝ R (x t) (Q t - x t)‖ + ‖fderiv ℝ R (x t) (e t)‖ :=
          norm_add_le _ _
      _ ≤ ε + K * ‖e t‖ := add_le_add h1 h2
      _ = K * ‖e t‖ + ε := add_comm _ _
  have he0 : ‖e 0‖ ≤ 0 := by simp [he, hv, hΦ0]
  have hg := norm_le_gronwallBound_of_norm_deriv_right_le (f := e) hcont.continuousOn
    (fun t _ => (he' t).hasDerivWithinAt) he0 hbound T ⟨hT, le_rfl⟩
  rw [gronwallBound_of_K_ne_0 hK.ne', sub_zero] at hg
  simp only [zero_mul, zero_add] at hg
  have hgoal : Q T - x T - Φ T (Q 0 - x 0) = e T := rfl
  rw [hgoal]
  refine hg.trans ?_
  have hε0 : 0 ≤ ε := by positivity
  calc ε / K * (Real.exp (K * T) - 1) ≤ ε / K * C := by
        apply mul_le_mul_of_nonneg_left (by rw [hC]; linarith) (div_nonneg hε0 hK.le)
    _ = η * ‖v‖ := by
        rw [hε]; field_simp

lemma inj_bound {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    (L : E →L[ℝ] F) (hinj : Function.Injective L) : ∃ c > 0, ∀ v, ‖v‖ ≤ c * ‖L v‖ := by
  have hcl : IsClosed (Set.range L) := by
    have := (LinearMap.range L.toLinearMap).closed_of_finiteDimensional
    simpa [LinearMap.coe_range] using this
  obtain ⟨K, hK⟩ := L.antilipschitz_of_injective_of_isClosed_range hinj hcl
  refine ⟨K + 1, by positivity, fun v => ?_⟩
  have := hK.le_mul_dist v 0
  simp only [dist_zero_right, map_zero] at this
  exact this.trans (mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _))

lemma fixed_unique {R : E → E} {x : ℝ → E} {Φ : ℝ → E →L[ℝ] E} {T : ℝ}
    (hxper : ∀ t, x (t + T) = x t)
    (hde : ∀ η > 0, ∃ r > 0, ∀ Q : ℝ → E, (∀ t, HasDerivAt Q (R (Q t)) t) →
      dist (Q 0) (x 0) < r → ‖Q T - x T - Φ T (Q 0 - x 0)‖ ≤ η * ‖Q 0 - x 0‖)
    (ℓ g0 : E →L[ℝ] ℝ) (G : E → ℝ) (hG : HasFDerivAt G g0 (x 0)) (hG1 : G (x 0) = 1)
    (hnd : ∀ v, ℓ v = 0 → g0 v = 0 → Φ T v = v → v = 0) :
    ∃ r0 > 0, ∀ Q : ℝ → E, (∀ t, HasDerivAt Q (R (Q t)) t) → (∀ t, Q (t + T) = Q t) →
      G (Q 0) = 1 → ℓ (Q 0 - x 0) = 0 → dist (Q 0) (x 0) < r0 → Q 0 = x 0 := by
  set L : E →L[ℝ] E × ℝ × ℝ := (Φ T - ContinuousLinearMap.id ℝ E).prod (ℓ.prod g0) with hLdef
  have hinj : Function.Injective L := by
    refine (injective_iff_map_eq_zero L).2 ?_
    intro v hv
    have hv' : L v = 0 := hv
    simp only [hLdef, ContinuousLinearMap.prod_apply, Prod.mk_eq_zero,
      ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply, sub_eq_zero] at hv'
    exact hnd v hv'.2.1 hv'.2.2 hv'.1
  obtain ⟨c, hc, hcL⟩ := inj_bound L hinj
  have hη : (0 : ℝ) < 1 / (4 * c) := by positivity
  obtain ⟨r1, hr1, hr1'⟩ := hde _ hη
  have hGo := hG.isLittleO.bound hη
  obtain ⟨r2, hr2, hr2'⟩ := Metric.eventually_nhds_iff.1 hGo
  refine ⟨min r1 r2, lt_min hr1 hr2, ?_⟩
  intro Q hQ hQper hGQ hℓ hd
  set v := Q 0 - x 0 with hv
  have hQT : Q T = Q 0 := by simpa using hQper 0
  have hxT : x T = x 0 := by simpa using hxper 0
  have h1 := hr1' Q hQ (lt_of_lt_of_le hd (min_le_left _ _))
  rw [hQT, hxT] at h1
  have h2 := hr2' (y := Q 0) (lt_of_lt_of_le hd (min_le_right _ _))
  rw [hGQ, hG1, sub_self, zero_sub, norm_neg] at h2
  have hLv : ‖L v‖ ≤ 1 / (4 * c) * ‖v‖ := by
    simp only [hLdef, ContinuousLinearMap.prod_apply, ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.id_apply, Prod.norm_def, hℓ, norm_zero]
    refine max_le ?_ (max_le (by positivity) h2)
    rw [norm_sub_rev]
    have : Q 0 - x 0 - Φ T v = v - Φ T v := rfl
    rw [this] at h1; exact h1
  have := (hcL v).trans (mul_le_mul_of_nonneg_left hLv hc.le)
  have hv0 : ‖v‖ = 0 := by
    have : c * (1 / (4 * c) * ‖v‖) = ‖v‖ / 4 := by field_simp
    nlinarith [norm_nonneg v]
  rw [norm_eq_zero, hv, sub_eq_zero] at hv0
  exact hv0

lemma time_adjust {R : E → E} {x : ℝ → E} {T δ : ℝ} {K : NNReal} (hT : 0 < T) (hδ : 0 < δ)
    (hL : ∀ t, LipschitzOnWith K R (ball (x t) δ))
    (hx : ∀ t, HasDerivAt x (R (x t)) t) (hxper : ∀ t, x (t + T) = x t)
    (hRc : ContinuousAt R (x 0)) (ℓ : E →L[ℝ] ℝ) (hℓR : ℓ (R (x 0)) = 1) :
    ∀ r0 > 0, ∃ r1 > 0, ∀ Q : ℝ → E, (∀ t, HasDerivAt Q (R (Q t)) t) →
      (∀ t, Q (t + T) = Q t) → dist (Q 0) (x 0) < r1 →
      ∃ σ, ℓ (Q σ - x 0) = 0 ∧ dist (Q σ) (x 0) < r0 := by
  intro r0 hr0
  have hxc : Continuous x := continuous_iff_continuousAt.2 fun t => (hx t).continuousAt
  have hcont : ContinuousAt (fun y => ℓ (R y)) (x 0) := ℓ.continuous.continuousAt.comp hRc
  have hev : ∀ᶠ y in 𝓝 (x 0), (1 / 2 : ℝ) < ℓ (R y) := by
    have := hcont.eventually (lt_mem_nhds (show (1 / 2 : ℝ) < ℓ (R (x 0)) by rw [hℓR]; norm_num))
    exact this
  obtain ⟨r2, hr2, hr2'⟩ := Metric.eventually_nhds_iff.1 hev
  set ρ := min r0 r2 with hρ
  have hρpos : 0 < ρ := lt_min hr0 hr2
  have hxT : x T = x 0 := by simpa using hxper 0
  obtain ⟨s0, hs0, hs0'⟩ := Metric.continuousAt_iff.1 (hxc.continuousAt (x := T)) (ρ / 2)
    (by positivity)
  set s := min (s0 / 2) T with hs
  have hspos : 0 < s := lt_min (by positivity) hT
  have hsT : s ≤ T := min_le_right _ _
  have hss0 : s < s0 := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  set B := Real.exp (K * (T + s)) with hB
  have hBpos : 0 < B := Real.exp_pos _
  refine ⟨min (min (δ / B) (ρ / 2 / B)) (s / 2 / (‖ℓ‖ + 1)), by positivity, ?_⟩
  intro Q hQ hQper hd
  set ε := dist (Q 0) (x 0) with hε
  have hε1 : ε * B < δ := (lt_div_iff₀ hBpos).1 (lt_of_lt_of_le hd ((min_le_left _ _).trans
    (min_le_left _ _)))
  have hε2 : ε * B < ρ / 2 := (lt_div_iff₀ hBpos).1 (lt_of_lt_of_le hd ((min_le_left _ _).trans
    (min_le_right _ _)))
  have hε3 : ε * (‖ℓ‖ + 1) < s / 2 := (lt_div_iff₀ (by positivity)).1
    (lt_of_lt_of_le hd (min_le_right _ _))
  have hcl := traj_close hL hx hQ (a := 0) (b := T + s) (ε := ε) le_rfl
    (by rw [sub_zero]; exact hε1)
  have hnear : ∀ σ ∈ Icc (T - s) (T + s), dist (Q σ) (x 0) < ρ := by
    intro σ hσ
    have h1 : dist (Q σ) (x σ) < ρ / 2 := by
      refine lt_of_le_of_lt (hcl σ ⟨by linarith [hσ.1], hσ.2⟩) (lt_of_le_of_lt ?_ hε2)
      have : 0 ≤ ε := dist_nonneg
      rw [hB, sub_zero]
      gcongr
      exact hσ.2
    have h2 : dist (x σ) (x T) < ρ / 2 := hs0' (by
      rw [Real.dist_eq, abs_lt]; constructor <;> linarith [hσ.1, hσ.2])
    rw [hxT] at h2
    linarith [dist_triangle (Q σ) (x σ) (x 0)]
  set g : ℝ → ℝ := fun σ => ℓ (Q σ - x 0) with hg
  have hgd : ∀ σ, HasDerivAt g (ℓ (R (Q σ))) σ := by
    intro σ
    exact ℓ.hasFDerivAt.comp_hasDerivAt σ ((hQ σ).sub_const (x 0))
  have hgc : Continuous g := continuous_iff_continuousAt.2 fun σ => (hgd σ).continuousAt
  have hmono : MonotoneOn (fun σ => g σ - σ / 2) (Icc (T - s) (T + s)) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc _ _)
      (f' := fun σ => ℓ (R (Q σ)) - 1 / 2)
    · exact (hgc.sub (continuous_id.div_const 2)).continuousOn
    · intro σ _
      exact ((hgd σ).sub ((hasDerivAt_id σ).div_const 2)).hasDerivWithinAt.congr_deriv
        (by simp)
    · intro σ hσ
      rw [interior_Icc] at hσ
      have := hr2' (hnear σ (Ioo_subset_Icc_self hσ) |>.trans_le (min_le_right _ _))
      linarith
  have hgT : |g T| < s / 2 := by
    have : g T = ℓ (Q 0 - x 0) := by simp [hg, show Q T = Q 0 by simpa using hQper 0]
    rw [this]
    refine lt_of_le_of_lt (ℓ.le_opNorm _) ?_
    rw [← dist_eq_norm]
    nlinarith [dist_nonneg (x := Q 0) (y := x 0), norm_nonneg ℓ]
  have hTm : T ∈ Icc (T - s) (T + s) := ⟨by linarith, by linarith⟩
  have hlo := hmono ⟨le_rfl, by linarith⟩ hTm (by linarith : T - s ≤ T)
  have hhi := hmono hTm ⟨by linarith, le_rfl⟩ (by linarith : T ≤ T + s)
  simp only at hlo hhi
  rw [abs_lt] at hgT
  have hIVT := intermediate_value_Icc (by linarith : T - s ≤ T + s) hgc.continuousOn
    (show (0 : ℝ) ∈ Icc (g (T - s)) (g (T + s)) from ⟨by linarith, by linarith⟩)
  obtain ⟨σ, hσ, hgσ⟩ := hIVT
  exact ⟨σ, hgσ, lt_of_lt_of_le (hnear σ hσ) (min_le_left _ _)⟩

theorem core {R : E → E} {U : Set E} (hU : IsOpen U) (hR : ContDiffOn ℝ 1 R U)
    {x : ℝ → E} {T : ℝ} (hT : 0 < T) (hx : ∀ t, HasDerivAt x (R (x t)) t)
    (hxper : ∀ t, x (t + T) = x t) (hxU : ∀ t, x t ∈ U) {Φ : ℝ → E →L[ℝ] E}
    (hΦ0 : Φ 0 = ContinuousLinearMap.id ℝ E)
    (hΦ : ∀ t, HasDerivAt Φ ((fderiv ℝ R (x t)).comp (Φ t)) t)
    (ℓ g0 : E →L[ℝ] ℝ) (G : E → ℝ) (hG : HasFDerivAt G g0 (x 0)) (hG1 : G (x 0) = 1)
    (hℓR : ℓ (R (x 0)) = 1) (hnd : ∀ v, ℓ v = 0 → g0 v = 0 → Φ T v = v → v = 0) :
    ∃ W : Set E, IsOpen W ∧ range x ⊆ W ∧ ∀ Q : ℝ → E, (∀ t, HasDerivAt Q (R (Q t)) t) →
      (∀ t, Q (t + T) = Q t) → (∀ t, G (Q t) = 1) → (∃ τ, Q τ ∈ W) → range Q ⊆ range x := by
  have hxc : Continuous x := continuous_iff_continuousAt.2 fun t => (hx t).continuousAt
  obtain ⟨δ, hδ, K, hK, hL, hA, hrem⟩ := setup hU hR hT hxc hxper hxU
  have hde := deriv_est hT.le hK hL hA hrem hx hΦ0 hΦ
  obtain ⟨r0, hr0, hfix⟩ := fixed_unique hxper hde ℓ g0 G hG hG1 hnd
  have hRc : ContinuousAt R (x 0) := hR.continuousOn.continuousAt (hU.mem_nhds (hxU 0))
  obtain ⟨r1, hr1, hadj⟩ := time_adjust hT hδ hL hx hxper hRc ℓ hℓR r0 hr0
  set C := Real.exp (K * T) with hC
  have hCpos : 0 < C := Real.exp_pos _
  set ε0 := min (r1 / C) (δ / C) / 2 with hε0
  have hε0pos : 0 < ε0 := by positivity
  have hε0C1 : ε0 * C < r1 := by
    have : ε0 < r1 / C := by
      rw [hε0]; linarith [min_le_left (r1 / C) (δ / C), div_pos hr1 hCpos]
    exact (lt_div_iff₀ hCpos).1 this
  have hε0C2 : ε0 * C < δ := by
    have : ε0 < δ / C := by
      rw [hε0]; linarith [min_le_right (r1 / C) (δ / C), div_pos hδ hCpos]
    exact (lt_div_iff₀ hCpos).1 this
  refine ⟨⋃ τ, ball (x τ) ε0, isOpen_iUnion fun _ => isOpen_ball, ?_, ?_⟩
  · rintro _ ⟨t, rfl⟩; exact mem_iUnion.2 ⟨t, mem_ball_self hε0pos⟩
  intro Q hQ hQper hQG ⟨s, hs⟩
  obtain ⟨τ, hτ⟩ := mem_iUnion.1 hs
  obtain ⟨τ', hτ', hxτ⟩ := Function.Periodic.exists_mem_Ico₀ (c := T) (f := x) hxper hT τ
  set Q1 : ℝ → E := fun t => Q (t + (s - τ')) with hQ1
  have hQ1d : ∀ t, HasDerivAt Q1 (R (Q1 t)) t := fun t => (hQ _).comp_add_const t _
  have hQ1per : ∀ t, Q1 (t + T) = Q1 t := by
    intro t; simp only [hQ1]; rw [show t + T + (s - τ') = t + (s - τ') + T by ring, hQper]
  have hQ1τ : Q1 τ' = Q s := by simp only [hQ1]; congr 1; ring
  have hcl := traj_close hL hx hQ1d (a := τ') (b := T) (ε := ε0)
    (by rw [hQ1τ, ← hxτ]; exact (mem_ball.1 hτ).le)
    (by
      refine lt_of_le_of_lt ?_ hε0C2
      rw [hC]; gcongr; linarith [hτ'.1])
  have hT1 := hcl T ⟨hτ'.2.le, le_rfl⟩
  have hQ1T : Q1 T = Q1 0 := by simpa using hQ1per 0
  have hxT : x T = x 0 := by simpa using hxper 0
  rw [hQ1T, hxT] at hT1
  have hd1 : dist (Q1 0) (x 0) < r1 := by
    refine lt_of_le_of_lt hT1 (lt_of_le_of_lt ?_ hε0C1)
    rw [hC]; gcongr; linarith [hτ'.1]
  obtain ⟨σ, hσℓ, hσd⟩ := hadj Q1 hQ1d hQ1per hd1
  set Q2 : ℝ → E := fun t => Q1 (t + σ) with hQ2
  have hQ2d : ∀ t, HasDerivAt Q2 (R (Q2 t)) t := fun t => (hQ1d _).comp_add_const t _
  have hQ2per : ∀ t, Q2 (t + T) = Q2 t := by
    intro t; simp only [hQ2]; rw [show t + T + σ = t + σ + T by ring, hQ1per]
  have hQ20 : Q2 0 = x 0 := by
    apply hfix Q2 hQ2d hQ2per
    · simp only [hQ2, hQ1]; exact hQG _
    · simpa [hQ2] using hσℓ
    · simpa [hQ2] using hσd
  have hfwd : ∀ t, 0 ≤ t → Q2 t = x t := by
    intro t ht
    have := traj_close hL hx hQ2d (a := 0) (b := t) (ε := 0) (by rw [hQ20, dist_self])
      (by rw [zero_mul]; exact hδ) t ⟨ht, le_rfl⟩
    rw [zero_mul] at this
    exact dist_le_zero.1 this
  rintro _ ⟨u, rfl⟩
  obtain ⟨w, hw, hQw⟩ := Function.Periodic.exists_mem_Ico₀ (c := T) (f := Q2) hQ2per hT
    (u - (s - τ') - σ)
  refine ⟨w, ?_⟩
  rw [← hfwd w hw.1, ← hQw]
  simp only [hQ2, hQ1]
  congr 1; ring

end IsoCore

namespace IsoSpec
open FiniteEnergyPlane
open scoped ContDiff

variable {n : ℕ}

lemma contDiff_j0 : ContDiff ℝ ∞ (j0 : V n → V n) := by
  refine contDiff_pi.2 fun k => ?_
  unfold j0
  by_cases h : (k : ℕ) % 2 = 0
  · simp only [h, dite_true]
    exact (contDiff_apply ℝ ℝ _).neg
  · simp only [h, dite_false]
    exact contDiff_apply ℝ ℝ _

lemma contDiff_hamVF (H : V n → ℝ) (hH : ContDiff ℝ ∞ H) : ContDiff ℝ ∞ (hamVF H) := by
  have hg : ContDiff ℝ ∞ (grad H) := by
    refine contDiff_pi.2 fun k => ?_
    exact (hH.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
  exact contDiff_j0.comp hg

lemma contDiff_liouville : ContDiff ℝ ∞ (fun p : V n × V n => liouville p.1 p.2) := by
  unfold liouville omega0 dot
  refine ContDiff.div_const (ContDiff.sum fun k _ => ?_) _
  exact ((contDiff_apply ℝ ℝ k).comp (contDiff_j0.comp contDiff_fst)).mul
    ((contDiff_apply ℝ ℝ k).comp contDiff_snd)

lemma liouvilleCLM_apply (x v : V n) : liouvilleCLM x v = liouville x v := by
  simp [liouvilleCLM, liouville, omega0, dot, Finset.sum_div, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

end IsoSpec

open FiniteEnergyPlane
open scoped ContDiff

theorem solution {n : ℕ} (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H) (P : ReebOrbit H)
    (hP : P.IsNondegenerate) : P.IsIsolated := by
  set D : V n → ℝ := fun y => liouville y (hamVF H y) with hDdef
  have hD : ContDiff ℝ ∞ D := by
    have h1 := IsoSpec.contDiff_liouville (n := n)
    have h2 := IsoSpec.contDiff_hamVF H hH.1
    exact h1.comp (contDiff_id.prodMk h2)
  set U : Set (V n) := {y | 0 < D y} with hUdef
  have hU : IsOpen U := isOpen_lt continuous_const hD.continuous
  have hR : ContDiffOn ℝ 1 (reeb H) U := by
    have : reeb H = fun y => (D y)⁻¹ • hamVF H y := rfl
    rw [this]
    have h1 : ContDiffOn ℝ ∞ (fun y => (D y)⁻¹) U :=
      hD.contDiffOn.inv fun y hy => ne_of_gt hy
    have h2 : ContDiffOn ℝ ∞ (hamVF H) U := (IsoSpec.contDiff_hamVF H hH.1).contDiffOn
    exact (h1.smul h2).of_le (by simp)
  have hxU : ∀ t, P.x t ∈ U := fun t => (reeb_spec H hH (P.x t) (P.mem t)).1
  obtain ⟨Φ, hΦ, -⟩ := (linReebFlow_spec H hH P).1
  have hHd : HasFDerivAt H (fderiv ℝ H (P.x 0)) (P.x 0) :=
    (hH.1.differentiable (by simp) _).hasFDerivAt
  obtain ⟨W, hWo, hWsub, hW⟩ := IsoCore.core hU hR P.T_pos P.hasDerivAt P.periodic hxU hΦ.1 hΦ.2
    (liouvilleCLM (P.x 0)) (fderiv ℝ H (P.x 0)) H hHd (P.mem 0)
    (by rw [IsoSpec.liouvilleCLM_apply]; exact (reeb_spec H hH (P.x 0) (P.mem 0)).2.1)
    (fun v h1 h2 h3 => hP Φ hΦ v ⟨by rwa [IsoSpec.liouvilleCLM_apply] at h1, h2⟩ h3)
  refine ⟨W, hWo, hWsub, fun Q hQT hmeet => ?_⟩
  exact hW Q.x Q.hasDerivAt (fun t => by rw [← hQT]; exact Q.periodic t) Q.mem hmeet
