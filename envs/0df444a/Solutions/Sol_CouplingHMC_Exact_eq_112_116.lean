-- Prove2me | solution 1 for CouplingHMC.Exact.eq_112_116
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T02:20:05.229181+00:00
-- url     : https://prove2.me/submissions/f13ae395-28eb-4d9c-86d9-55caae20c4fa

import Mathlib
import Definitions.Def_CouplingHMC_Exact_Setting

open MeasureTheory ProbabilityTheory
open scoped ENNReal InnerProductSpace

open CouplingHMC.Exact in
theorem solution (L K ℛ T : ℝ) (hT : 0 < T) (hℛ : 0 ≤ ℛ) (hTc : StepCond L K ℛ T) :
    gammaC T ℛ * T ≤ 1 ∧ L * T ≤ gammaC T ℛ / 4 ∧ gammaC T ℛ * ℛ ≤ 1 / 4 ∧
      1 ≤ aC T * T ∧ 5 / 2 * (1 + gammaC T ℛ * T) * ℛ ≤ R1C T ℛ := by
  obtain ⟨_, hc2, hc3⟩ := hTc
  have hTi : T⁻¹ * T = 1 := inv_mul_cancel₀ hT.ne'
  have hTi0 : 0 < T⁻¹ := inv_pos.mpr hT
  have f1 : gammaC T ℛ ≤ T⁻¹ := by
    unfold gammaC; split_ifs
    · exact le_rfl
    · exact min_le_left _ _
  have f2 : gammaC T ℛ * ℛ ≤ 1 / 4 := by
    unfold gammaC; split_ifs with h
    · rw [h]; norm_num
    · have hR : 0 < ℛ := lt_of_le_of_ne hℛ (Ne.symm h)
      calc min T⁻¹ (ℛ⁻¹ / 4) * ℛ ≤ ℛ⁻¹ / 4 * ℛ :=
            mul_le_mul_of_nonneg_right (min_le_right _ _) hℛ
        _ = 1 / 4 := by rw [div_mul_eq_mul_div, inv_mul_cancel₀ hR.ne']
  have a1 : L * T ≤ T⁻¹ / 4 := by
    calc L * T = (L * T ^ 2) * T⁻¹ := by
          rw [eq_comm, mul_inv_eq_iff_eq_mul₀ hT.ne']; ring
      _ ≤ (1 / 4) * T⁻¹ := mul_le_mul_of_nonneg_right hc2 hTi0.le
      _ = T⁻¹ / 4 := by ring
  refine ⟨?_, ?_, f2, ?_, ?_⟩
  · calc gammaC T ℛ * T ≤ T⁻¹ * T := mul_le_mul_of_nonneg_right f1 hT.le
      _ = 1 := hTi
  · unfold gammaC; split_ifs with h
    · exact a1
    · have hR : 0 < ℛ := lt_of_le_of_ne hℛ (Ne.symm h)
      have hx : 16 * L * ℛ * T ≤ 1 := by nlinarith [sq_nonneg (16 * L * ℛ * T - 1)]
      have a2 : L * T ≤ ℛ⁻¹ / 16 := by
        calc L * T = (16 * L * ℛ * T) * ℛ⁻¹ / 16 := by
              field_simp
          _ ≤ 1 * ℛ⁻¹ / 16 := by
              apply div_le_div_of_nonneg_right _ (by norm_num)
              exact mul_le_mul_of_nonneg_right hx (inv_nonneg.mpr hℛ)
          _ = ℛ⁻¹ / 16 := by ring
      rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 4)]
      apply le_min <;> linarith
  · unfold aC; rw [hTi]
  · unfold R1C
    have : gammaC T ℛ * T * ℛ ≤ T := by
      calc gammaC T ℛ * T * ℛ = (gammaC T ℛ * ℛ) * T := by ring
        _ ≤ (1 / 4) * T := mul_le_mul_of_nonneg_right f2 hT.le
        _ ≤ T := by linarith
    nlinarith
