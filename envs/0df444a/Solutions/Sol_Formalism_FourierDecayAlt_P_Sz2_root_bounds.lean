-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Sz2.root_bounds
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:36:38.691787+00:00
-- url     : https://prove2.me/submissions/6ba4946c-9709-4677-b56d-2431ee209abb

import Definitions.Def_Formalism_HermitianCurvature_StatementSz
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MassRatioFormula
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CorollaryAOfPropositionA

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
theorem _root_.solution {P Ea C0 X : ℝ} {k : ℕ} (hP0 : 0 < P) (hk1 : 1 ≤ k) (hC0 : 1 ≤ C0)
    (hX0 : 0 ≤ X) (hX8 : 8 * X ≤ k) (hEa12 : 1 / 2 ≤ Ea) (hEa2 : Ea ≤ 2)
    (hlo : Real.exp (2 * X) / C0 ≤ Ea * P ^ k) (hhi : Ea * P ^ k ≤ Real.exp (2 * X) * C0) :
    (2 * C0) ^ (-(1 / (k : ℝ))) ≤ P ∧
      P ≤ (2 * C0) ^ (1 / (k : ℝ)) * Real.exp (1 / 4) ∧
      (2 * C0) ^ (1 / (k : ℝ)) * Real.exp (1 / 4) ≤ 2 * C0 * Real.exp (1 / 4) := by
  have hkne : k ≠ 0 := by omega
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk1
  have hkR1 : (1 : ℝ) ≤ k := by exact_mod_cast hk1
  have hC00 : 0 < C0 := by linarith
  have hPk0 : 0 < P ^ k := pow_pos hP0 _
  have hG20 : 0 < Real.exp (2 * X) := Real.exp_pos _
  have hG21 : 1 ≤ Real.exp (2 * X) := Real.one_le_exp (by linarith)
  have h2C : 0 < 2 * C0 := by linarith
  have hlow : (2 * C0)⁻¹ ≤ P ^ k := by
    have h1 : 1 / C0 ≤ Ea * P ^ k :=
      le_trans (div_le_div_of_nonneg_right hG21 hC00.le) hlo
    have h2 : Ea * P ^ k ≤ 2 * P ^ k := mul_le_mul_of_nonneg_right hEa2 hPk0.le
    have h3 : (2 * C0)⁻¹ = 1 / C0 / 2 := by field_simp
    rw [h3]
    linarith
  have hup : P ^ k ≤ 2 * C0 * Real.exp (2 * X) := by
    have h2 : 1 / 2 * P ^ k ≤ Ea * P ^ k := mul_le_mul_of_nonneg_right hEa12 hPk0.le
    linarith
  have hPr : (P ^ k) ^ ((k : ℝ)⁻¹) = P := Real.pow_rpow_inv_natCast hP0.le hkne
  have hkinv : 0 ≤ (k : ℝ)⁻¹ := by positivity
  refine ⟨?_, ?_, ?_⟩
  · rw [Real.rpow_neg h2C.le, ← Real.inv_rpow h2C.le, one_div]
    calc ((2 * C0)⁻¹) ^ ((k : ℝ)⁻¹) ≤ (P ^ k) ^ ((k : ℝ)⁻¹) :=
          Real.rpow_le_rpow (by positivity) hlow hkinv
      _ = P := hPr
  · rw [one_div]
    calc P = (P ^ k) ^ ((k : ℝ)⁻¹) := hPr.symm
      _ ≤ (2 * C0 * Real.exp (2 * X)) ^ ((k : ℝ)⁻¹) :=
          Real.rpow_le_rpow hPk0.le hup hkinv
      _ = (2 * C0) ^ ((k : ℝ)⁻¹) * Real.exp (2 * X) ^ ((k : ℝ)⁻¹) :=
          Real.mul_rpow h2C.le hG20.le
      _ ≤ (2 * C0) ^ ((k : ℝ)⁻¹) * Real.exp (1 / 4) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          rw [← Real.exp_mul]
          apply Real.exp_le_exp.mpr
          rw [← div_eq_mul_inv, div_le_iff₀ hkR]
          linarith
  · apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
    calc (2 * C0) ^ (1 / (k : ℝ)) ≤ (2 * C0) ^ (1 : ℝ) := by
          apply Real.rpow_le_rpow_of_exponent_le (by linarith)
          rw [div_le_iff₀ hkR]; linarith
      _ = 2 * C0 := Real.rpow_one _
end Formalism.FourierDecayAlt.P.Sz2
