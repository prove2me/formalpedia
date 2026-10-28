-- Prove2me | solution 1 for FunctionalInequalities.Analysis.truncatedConjugate_centered_spec_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T13:33:47.620199+00:00
-- url     : https://prove2.me/submissions/7d5c3006-da2e-4b19-9457-4acaac65f4f7

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Convex_Caffarelli
import Theorems.Thm_FunctionalInequalities_Analysis_convexOn_truncatedConjugate_readable
import Theorems.Thm_FunctionalInequalities_Analysis_exists_truncatedConjugate_eq_readable

noncomputable section
open Set Metric
open scoped RealInnerProductSpace
section LT11F2TruncatedConjugate
section FiniteDimensional
variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
/-- **Zeros of the centred truncated conjugate are the subgradients**: for convex `u` and
`‖xc‖ < M`, `f p := truncatedConjugate u M p − ⟪p, xc⟫ + u xc` is nonnegative, vanishes exactly at the
subgradients of `u` at `xc`, and has compact sublevel sets. -/
theorem solution {u : E → ℝ} (hconv : ConvexOn ℝ univ u) {M : ℝ} {xc : E}
    (hxc : ‖xc‖ < M) :
    (∀ p, 0 ≤ FunctionalInequalities.Analysis.truncatedConjugate u M p - ⟪p, xc⟫ + u xc) ∧
    (∀ p, FunctionalInequalities.Analysis.truncatedConjugate u M p - ⟪p, xc⟫ + u xc = 0 ↔ ∀ y, u xc + ⟪p, y - xc⟫ ≤ u y) ∧
    ∀ R : ℝ, IsCompact {p | FunctionalInequalities.Analysis.truncatedConjugate u M p - ⟪p, xc⟫ + u xc ≤ R} := by
  have hu : Continuous u :=
    continuousOn_univ.mp (ConvexOn.continuousOn isOpen_univ hconv)
  have hM : 0 ≤ M := (norm_nonneg xc).trans hxc.le
  have hxc_mem : xc ∈ closedBall (0 : E) M :=
    mem_closedBall_zero_iff.mpr hxc.le
  have hnonneg (p : E) :
      0 ≤ FunctionalInequalities.Analysis.truncatedConjugate u M p - ⟪p, xc⟫ + u xc := by
    have h := (FunctionalInequalities.Analysis.exists_truncatedConjugate_eq_readable hu hM p).2 xc hxc_mem
    linarith
  refine ⟨hnonneg, ?_, ?_⟩
  · intro p
    constructor
    · intro hp
      have htilt : ConvexOn ℝ univ (fun x => u x - ⟪p, x⟫) := by
        refine ⟨convex_univ, ?_⟩
        intro x hx y hy a b ha hb hab
        have hc := hconv.2 hx hy ha hb hab
        change u (a • x + b • y) - ⟪p, a • x + b • y⟫ ≤
          a * (u x - ⟪p, x⟫) + b * (u y - ⟪p, y⟫)
        rw [inner_add_right, real_inner_smul_right, real_inner_smul_right]
        change u (a • x + b • y) ≤ a * u x + b * u y at hc
        linarith
      have hmin :
          IsMinOn (fun x => u x - ⟪p, x⟫) (closedBall (0 : E) M) xc := by
        intro x hx
        have h := (FunctionalInequalities.Analysis.exists_truncatedConjugate_eq_readable hu hM p).2 x hx
        change u xc - ⟪p, xc⟫ ≤ u x - ⟪p, x⟫
        linarith
      have hnbhd : closedBall (0 : E) M ∈ nhds xc :=
        Filter.mem_of_superset
          (isOpen_ball.mem_nhds (mem_ball_zero_iff.mpr hxc))
          ball_subset_closedBall
      have hglobal :=
        IsMinOn.of_isLocalMin_of_convex_univ (hmin.isLocalMin hnbhd) htilt
      intro y
      have hy := hglobal y
      rw [inner_sub_right]
      linarith
    · intro hp
      obtain ⟨x, hx, heq⟩ := (FunctionalInequalities.Analysis.exists_truncatedConjugate_eq_readable hu hM p).1
      have hs := hp x
      rw [inner_sub_right] at hs
      have hn := hnonneg p
      rw [heq] at hn ⊢
      linarith
  · intro R
    have htc : Continuous (FunctionalInequalities.Analysis.truncatedConjugate u M) :=
      continuousOn_univ.mp
        (ConvexOn.continuousOn isOpen_univ (FunctionalInequalities.Analysis.convexOn_truncatedConjugate_readable hu hM))
    have hf : Continuous (fun p => FunctionalInequalities.Analysis.truncatedConjugate u M p - ⟪p, xc⟫ + u xc) :=
      (htc.sub (continuous_id.inner continuous_const)).add continuous_const
    obtain ⟨C, hC⟩ :=
      (isCompact_closedBall (0 : E) M).exists_bound_of_continuousOn hu.continuousOn
    have hd : 0 < M - ‖xc‖ := sub_pos.mpr hxc
    apply Metric.isCompact_of_isClosed_isBounded (isClosed_le hf continuous_const)
    apply (Metric.isBounded_iff_subset_closedBall (0 : E)).2
    refine ⟨max 0 ((R + C - u xc) / (M - ‖xc‖)), ?_⟩
    intro p hp
    change FunctionalInequalities.Analysis.truncatedConjugate u M p - ⟪p, xc⟫ + u xc ≤ R at hp
    apply mem_closedBall_zero_iff.mpr
    by_cases hp0 : p = 0
    · subst p
      rw [norm_zero]
      exact le_max_left _ _
    · have hn : ‖p‖ ≠ 0 := norm_ne_zero_iff.mpr hp0
      let x : E := xc + ((M - ‖xc‖) / ‖p‖) • p
      have hnorm : ‖((M - ‖xc‖) / ‖p‖) • p‖ = M - ‖xc‖ := by
        rw [norm_smul, Real.norm_eq_abs,
          abs_of_nonneg (div_nonneg hd.le (norm_nonneg p)), div_mul_cancel₀ _ hn]
      have hx : x ∈ closedBall (0 : E) M := by
        apply mem_closedBall_zero_iff.mpr
        calc
          ‖x‖ ≤ ‖xc‖ + ‖((M - ‖xc‖) / ‖p‖) • p‖ := norm_add_le _ _
          _ = M := by rw [hnorm]; ring
      have hinner : ⟪p, x⟫ = ⟪p, xc⟫ + (M - ‖xc‖) * ‖p‖ := by
        dsimp only [x]
        rw [inner_add_right, real_inner_smul_right, real_inner_self_eq_norm_sq]
        congr 1
        field_simp
      have hux : u x ≤ C := by
        have hc := hC x hx
        rw [Real.norm_eq_abs] at hc
        exact (le_abs_self (u x)).trans hc
      have hdom := (FunctionalInequalities.Analysis.exists_truncatedConjugate_eq_readable hu hM p).2 x hx
      rw [hinner] at hdom
      calc
        ‖p‖ ≤ (R + C - u xc) / (M - ‖xc‖) := by
          apply (le_div_iff₀ hd).2
          nlinarith
        _ ≤ max 0 ((R + C - u xc) / (M - ‖xc‖)) := le_max_right _ _
