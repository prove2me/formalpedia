-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.PrimesInProgressions.ell_bounds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T07:37:51.344094+00:00
-- url     : https://prove2.me/submissions/fa697586-0116-4e10-ba35-42376a85fdeb

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_DeuringHeilbronnM
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTZSumB

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Complex Classical
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.PrimesInProgressions
open Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds Formalism.ZeroFreeDirichlet
namespace Formalism.HermitianLattices.Ext.PrimesInProgressions
theorem _root_.solution (M : ℕ) (hM : 8 ≤ M) (A₁ : ℝ) (hA : 1 ≤ A₁) :
    2 ≤ Real.log M ∧ Real.log M ≤ Real.log ((M : ℝ) * ((M : ℝ) ^ A₁ + 3)) ∧
      Real.log ((M : ℝ) * ((M : ℝ) ^ A₁ + 3)) ≤ (A₁ + 2) * Real.log M := by
  have hM' : (8 : ℝ) ≤ M := by exact_mod_cast hM
  have hM0 : (0 : ℝ) < M := by linarith
  have hp : (M : ℝ) ≤ (M : ℝ) ^ A₁ := by
    conv_lhs => rw [← Real.rpow_one (M : ℝ)]
    exact Real.rpow_le_rpow_of_exponent_le (by linarith) hA
  refine ⟨?_, ?_, ?_⟩
  · have h1 : Real.log 8 ≤ Real.log M := Real.log_le_log (by norm_num) hM'
    have h2 : Real.log 8 = 3 * Real.log 2 := by
      rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]; norm_num
    have := Real.log_two_gt_d9
    linarith
  · apply Real.log_le_log hM0
    nlinarith
  · have h1 : (M : ℝ) * ((M : ℝ) ^ A₁ + 3) ≤ (M : ℝ) ^ (A₁ + 2) := by
      rw [Real.rpow_add hM0, show ((M : ℝ) ^ (2 : ℝ)) = (M : ℝ) * M by
        rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; ring]
      have h2 : (M : ℝ) ^ A₁ + 3 ≤ (M : ℝ) ^ A₁ * M := by nlinarith
      calc (M : ℝ) * ((M : ℝ) ^ A₁ + 3) ≤ (M : ℝ) * ((M : ℝ) ^ A₁ * M) :=
            mul_le_mul_of_nonneg_left h2 hM0.le
        _ = _ := by ring
    calc _ ≤ Real.log ((M : ℝ) ^ (A₁ + 2)) := Real.log_le_log (by positivity) h1
      _ = _ := Real.log_rpow hM0 _
end Formalism.HermitianLattices.Ext.PrimesInProgressions
