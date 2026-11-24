-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Sz2.eaSize
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:52:14.250796+00:00
-- url     : https://prove2.me/submissions/bb99b2b7-f536-412c-a6bb-38dfb53028ed

import Definitions.Def_Formalism_HermitianCurvature_StatementSz
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MassRatioFormula
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CorollaryAOfPropositionA
import Theorems.Thm_Formalism_FourierDecayAlt_P_Sz2_zetaTail
import Theorems.Thm_Formalism_FourierDecayAlt_P_Sz2_abs_log_one_sub_le
import Theorems.Thm_Formalism_FourierDecayAlt_P_Sz2_geom_le
import Theorems.Thm_Formalism_FourierDecayAlt_P_Sz2_inv_pow_bounds
import Theorems.Thm_Formalism_FourierDecayAlt_P_Sz2_prod_one_sub

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Sz2
open Finset Formalism.FourierDecayAlt.Sz
namespace Formalism.FourierDecayAlt.P.Sz2
theorem _root_.solution : EaSize := by
  intro ι _ S hOk hL hk _ _
  have hA : ∀ M ∈ Ioc S.k S.n, 0 < S.Lv M := fun M hM =>
    (hL M (mem_Ioc.mp hM).1 (mem_Ioc.mp hM).2).1
  have hApos : 0 < ∏ M ∈ Ioc S.k S.n, S.Lv M := prod_pos hA
  obtain ⟨hB1, hB1'⟩ := prod_one_sub S.g1 hOk.hg1 S.k S.n
  obtain ⟨hB2, hB2'⟩ := prod_one_sub S.g2 hOk.hg2 S.k S.n
  obtain ⟨t1, t2, t3⟩ := inv_pow_bounds S.T S.k hOk.hT hOk.hk
  have hT : 0 < 1 - ((S.T : ℝ) ^ S.k)⁻¹ := by linarith
  have hT' : |Real.log (1 - ((S.T : ℝ) ^ S.k)⁻¹)| ≤ 2 / 2 ^ S.k := by
    have := abs_log_one_sub_le t1 (t2.trans t3)
    calc _ ≤ 2 * ((S.T : ℝ) ^ S.k)⁻¹ := this
      _ ≤ 2 * (1 / 2 ^ S.k) := by linarith
      _ = 2 / 2 ^ S.k := by ring
  have hf : (0 : ℝ) ≤ S.f := Nat.cast_nonneg _
  have hA' : |Real.log (∏ M ∈ Ioc S.k S.n, S.Lv M)| ≤ (S.f : ℝ) * (2 / 2 ^ S.k) := by
    rw [Real.log_prod (fun j hj => (hA j hj).ne')]
    calc |∑ M ∈ Ioc S.k S.n, Real.log (S.Lv M)|
        ≤ ∑ M ∈ Ioc S.k S.n, |Real.log (S.Lv M)| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ M ∈ Ioc S.k S.n, (S.f : ℝ) * (2 * (1 / (2 : ℝ) ^ M)) := by
          apply sum_le_sum
          intro M hM
          have hM1 := (mem_Ioc.mp hM).1
          have h1 := (hL M hM1 (mem_Ioc.mp hM).2).2
          have h2 := zetaTail M (by omega)
          calc _ ≤ _ := h1
            _ ≤ (S.f : ℝ) * (2 / 2 ^ M) := mul_le_mul_of_nonneg_left h2 hf
            _ = _ := by ring
      _ = (S.f : ℝ) * (2 * ∑ M ∈ Ioc S.k S.n, 1 / (2 : ℝ) ^ M) := by rw [mul_sum, mul_sum]
      _ ≤ (S.f : ℝ) * (2 * (1 / 2 ^ S.k)) := by
          have := geom_le S.k S.n
          apply mul_le_mul_of_nonneg_left _ hf
          linarith
      _ = _ := by ring
  have hEa : 0 < S.Ea := by
    unfold SizeData.Ea
    positivity
  refine ⟨hEa, ?_⟩
  have hlog : Real.log S.Ea = Real.log (∏ M ∈ Ioc S.k S.n, S.Lv M) +
      ((S.f : ℝ) * Real.log (∏ j ∈ Ioc S.k S.n, (1 - ((S.g1 : ℝ) ^ j)⁻¹)) +
        (S.f : ℝ) * Real.log (∏ j ∈ Ioc S.k S.n, (1 - ((S.g2 : ℝ) ^ j)⁻¹))) -
      (S.f : ℝ) * Real.log (1 - ((S.T : ℝ) ^ S.k)⁻¹) := by
    unfold SizeData.Ea
    rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity), Real.log_inv, Real.log_pow, Real.log_pow,
      Real.log_pow]
    ring
  rw [hlog]
  have a1 := abs_le.mp hA'
  have a2 := abs_le.mp hB1'
  have a3 := abs_le.mp hB2'
  have a4 := abs_le.mp hT'
  have b2l := mul_le_mul_of_nonneg_left a2.1 hf
  have b2r := mul_le_mul_of_nonneg_left a2.2 hf
  have b3l := mul_le_mul_of_nonneg_left a3.1 hf
  have b3r := mul_le_mul_of_nonneg_left a3.2 hf
  have b4l := mul_le_mul_of_nonneg_left a4.1 hf
  have b4r := mul_le_mul_of_nonneg_left a4.2 hf
  have e8 : (S.f : ℝ) * (8 / 2 ^ S.k) = 4 * ((S.f : ℝ) * (2 / 2 ^ S.k)) := by ring
  rw [e8, abs_le]
  constructor <;> linarith
end Formalism.FourierDecayAlt.P.Sz2
