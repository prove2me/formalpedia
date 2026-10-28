-- Prove2me | solution 1 for FunctionalInequalities.Analysis.contact_stepA_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T13:31:14.934712+00:00
-- url     : https://prove2.me/submissions/7e61700b-bab9-486e-81b4-7a0037b700d9

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Convex_Caffarelli

noncomputable section
open Set Metric
open scoped RealInnerProductSpace
section LT11E7LocalizedContactLemma
open MeasureTheory Set Metric
open scoped RealInnerProductSpace ENNReal
section InnerProduct
variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]
section FiniteDimensional
variable [FiniteDimensional ℝ E]
 lemma solution
    [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
    {v : E → ℝ} {S : Set E} {A t : ℝ} (ht : 0 < t)
    (hball : ball (0 : E) 1 ⊆ S)
    (hlo : ∀ x ∈ S, -2 * t ≤ v x)
    (hhi : ∀ x ∈ S, v x ≤ 0)
    (hA : A * ((volume : Measure E) (ball (0 : E) (1 / 2))).toReal ≤
      (volume (FunctionalInequalities.Analysis.subgradientImage v (ball (0 : E) (1 / 2)))).toReal) :
    A ≤ (8 * t) ^ Module.finrank ℝ E := by
  let n := Module.finrank ℝ E
  have hsub :
      FunctionalInequalities.Analysis.subgradientImage v (ball (0 : E) (1 / 2)) ⊆
        closedBall (0 : E) (4 * t) := by
    rintro p ⟨z, hz, hp⟩
    have hzNorm : ‖z‖ < 1 / 2 := by
      simpa only [mem_ball, dist_zero_right] using hz
    have hzS : z ∈ S :=
      hball ((ball_subset_ball (by norm_num : (1 / 2 : ℝ) ≤ 1)) hz)
    have hpNorm : ‖p‖ ≤ 4 * t := by
      by_cases hp0 : p = 0
      · simp only [hp0, norm_zero]
        positivity
      have hpn : 0 < ‖p‖ := norm_pos_iff.mpr hp0
      let q : E := ‖p‖⁻¹ • p
      have hq : ‖q‖ = 1 := by
        dsimp only [q]
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hpn)]
        exact inv_mul_cancel₀ hpn.ne'
      let y : E := z + (1 / 2 : ℝ) • q
      have hyNorm : ‖y‖ < 1 := by
        calc
          ‖y‖ ≤ ‖z‖ + ‖(1 / 2 : ℝ) • q‖ := norm_add_le _ _
          _ = ‖z‖ + 1 / 2 := by
            rw [norm_smul, hq]
            norm_num
          _ < 1 := by linarith
      have hyS : y ∈ S := hball (by
        simpa only [mem_ball, dist_zero_right] using hyNorm)
      have hpair : ⟪p, y - z⟫ = ‖p‖ / 2 := by
        dsimp only [y, q]
        simp only [add_sub_cancel_left, real_inner_smul_right,
          real_inner_self_eq_norm_sq]
        field_simp [hpn.ne']
      have hs := hp y
      rw [hpair] at hs
      have hzlo := hlo z hzS
      have hyhi := hhi y hyS
      linarith
    simpa only [mem_closedBall, dist_zero_right] using hpNorm
  have hballfin :
      (volume : Measure E) (closedBall (0 : E) (4 * t)) ≠ ∞ :=
    Metric.isBounded_closedBall.measure_lt_top.ne
  have hmeasure := ENNReal.toReal_mono hballfin (measure_mono hsub)
  let V := ((volume : Measure E) (ball (0 : E) 1)).toReal
  have hV : 0 < V := ENNReal.toReal_pos
    (isOpen_ball.measure_pos volume ⟨0, mem_ball_self zero_lt_one⟩).ne'
    Metric.isBounded_ball.measure_lt_top.ne
  have hhalf :
      ((volume : Measure E) (ball (0 : E) (1 / 2))).toReal =
        (1 / 2 : ℝ) ^ n * V := by
    rw [Measure.addHaar_ball volume (0 : E) (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)]
  have hfour :
      ((volume : Measure E) (closedBall (0 : E) (4 * t))).toReal =
        (4 * t) ^ n * V := by
    rw [Measure.addHaar_closedBall volume (0 : E)
      (show 0 ≤ 4 * t by positivity)]
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)]
  have h := hA.trans hmeasure
  rw [hhalf, hfour] at h
  have hcancel : A * (1 / 2 : ℝ) ^ n ≤ (4 * t) ^ n := by
    apply le_of_mul_le_mul_right (a := V) _ hV
    simpa only [mul_assoc] using h
  have hpow :
      (8 * t) ^ n * (1 / 2 : ℝ) ^ n = (4 * t) ^ n := by
    rw [← mul_pow]
    congr 1
    ring
  apply le_of_mul_le_mul_right (a := (1 / 2 : ℝ) ^ n) _ (by positivity)
  rw [hpow]
  exact hcancel
