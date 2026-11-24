-- Prove2me | solution 1 for Formalism.L2.Th1.B.SAdd.sW_sq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:21:13.399191+00:00
-- url     : https://prove2.me/submissions/30d096af-70b0-410a-b41a-6c4ea70534be

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_FinalA
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementE
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_ConstantCoeffQuotientXSq
import Theorems.Thm_Formalism_L2_Th1_B_SAdd_eq_X_sq_mul_quotient
import Theorems.Thm_Formalism_L2_Th1_B_SAdd_constantCoeff_quotient_X_sq
import Theorems.Thm_Formalism_L2_Th1_B_SAdd_constantCoeff_half_log
import Theorems.Thm_Formalism_L2_Th1_B_fExp_add
import Theorems.Thm_Formalism_L2_Th1_B_fExp_fLog


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.B Formalism.L2.Th1.B.SAdd
open Formalism.InvariantFactorPaths.G7 (at1)
open PowerSeries
variable {K : Type} [Field K] [CharZero K]
namespace Formalism.L2.Th1.B.SAdd
theorem _root_.solution {w : PowerSeries K} (h0 : constantCoeff w = 0) (h1 : coeff 1 w = 0)
    (h2 : coeff 2 w = 1) : sW w ^ 2 = w := by
  have hL := constantCoeff_half_log h2
  have hadd : C (1 / 2 : K) * fLog (divByXSq w) + C (1 / 2 : K) * fLog (divByXSq w) = fLog (divByXSq w) := by
    rw [← add_mul, ← map_add, add_halves, map_one, one_mul]
  have hE := fExp_add (K := K) (ι := Unit) hL hL
  rw [hadd, fExp_fLog (constantCoeff_quotient_X_sq h2)] at hE
  conv_rhs => rw [eq_X_sq_mul_quotient h0 h1, hE]
  rw [sW]
  ring
end Formalism.L2.Th1.B.SAdd
