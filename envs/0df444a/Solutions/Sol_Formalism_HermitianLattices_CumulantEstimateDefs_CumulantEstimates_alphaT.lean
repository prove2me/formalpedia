-- Prove2me | solution 1 for Formalism.HermitianLattices.CumulantEstimateDefs.CumulantEstimates.alphaT
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:04:40.688805+00:00
-- url     : https://prove2.me/submissions/c4709281-7295-4109-9c7c-00ccbb9da76d

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_QuadraticFormLowerBound
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_HilbertSchmidtHalfBound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.CumulantEstimateDefs Formalism.HermitianLattices.CumulantEstimateDefs.CumulantEstimates
open Finset
namespace Formalism.HermitianLattices.CumulantEstimateDefs.CumulantEstimates
theorem _root_.solution : DecayExponentLowerBound := by
  unfold DecayExponentLowerBound
  intro C hC
  refine ⟨3, 2 * C + 2, by norm_num, by linarith, ?_⟩
  intro C₁ C₂ h1 h2 p q ε₀ Q₀ hp hq he0 he1 hQ
  dsimp only
  push_cast at hQ ⊢
  have hpR : (1:ℝ) ≤ p := by exact_mod_cast hp
  have hqR : (1:ℝ) ≤ q := by exact_mod_cast hq
  have hpq : (1:ℝ) ≤ (p:ℝ) * q := by nlinarith
  have hC2 : 0 < C₂ := by linarith
  have hN : (2:ℝ) ≤ 2 * (p:ℝ) * q := by nlinarith
  have hL : 2 / 3 < Real.log (2 * (p:ℝ) * q) := by
    have h2l : Real.log 2 ≤ Real.log (2 * (p:ℝ) * q) := Real.log_le_log (by norm_num) hN
    have h3 := Real.log_two_gt_d9
    have h4 : (2:ℝ) / 3 < 0.6931471803 := by norm_num
    linarith
  have hNL : 0 ≤ 2 * (p:ℝ) * q * Real.log (2 * (p:ℝ) * q) := by
    apply mul_nonneg <;> linarith
  have e1 : 3 * (2 * (p:ℝ) * q * Real.log (2 * (p:ℝ) * q)) ≤
      C₁ * (2 * (p:ℝ) * q * Real.log (2 * (p:ℝ) * q)) := mul_le_mul_of_nonneg_right h1 hNL
  have e2 : 2 * (p:ℝ) * q * (2 / 3) ≤ 2 * (p:ℝ) * q * Real.log (2 * (p:ℝ) * q) :=
    mul_le_mul_of_nonneg_left hL.le (by linarith)
  have hQ2 : 4 * ((p:ℝ) * q) ≤ Q₀ := by linarith
  refine ⟨?_, by linarith⟩
  set ε := ε₀ / (C₂ * ((p:ℝ) * q)) with hε
  have hD : 0 < C₂ * ((p:ℝ) * q) := mul_pos hC2 (by linarith)
  have hε0 : 0 < ε := div_pos he0 hD
  have hεm : ε * (C₂ * ((p:ℝ) * q)) = ε₀ := by
    rw [hε, div_mul_eq_mul_div, mul_div_assoc, div_self hD.ne', mul_one]
  have a1 : ε * C₂ ≤ ε * C₂ * ((p:ℝ) * q) := le_mul_of_one_le_right (mul_pos hε0 hC2).le hpq
  have a0 : C * ε ≤ (C₂ / 2) * ε := mul_le_mul_of_nonneg_right (by linarith) hε0.le
  have a2 : C * ε ≤ 1 / 4 := by linarith
  have b1 : C * ε * Q₀ ≤ 1 / 4 * Q₀ := mul_le_mul_of_nonneg_right a2 (by linarith)
  have c1 : (p:ℝ) + q ≤ 2 * ((p:ℝ) * q) := by
    nlinarith [mul_nonneg (sub_nonneg.2 hpR) (sub_nonneg.2 hqR)]
  have c2 := mul_le_mul_of_nonneg_right c1 hε0.le
  have c3 : 2 * ((p:ℝ) * q * ε) ≤ C₂ * ((p:ℝ) * q * ε) :=
    mul_le_mul_of_nonneg_right (by linarith) (mul_pos (by linarith) hε0).le
  linarith
end Formalism.HermitianLattices.CumulantEstimateDefs.CumulantEstimates
