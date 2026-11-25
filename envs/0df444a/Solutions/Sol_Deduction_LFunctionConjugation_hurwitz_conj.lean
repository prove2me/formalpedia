-- Prove2me | solution 1 for Deduction.LFunctionConjugation.hurwitz_conj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:57:11.5257+00:00
-- url     : https://prove2.me/submissions/7d472495-4f6e-4f98-afd1-9273661038a1

import Definitions.Def_Development_AutomorphicArithmetic_DedekindLFunctions_LandauZeroFreeCriterion
import Definitions.Def_Development_AutomorphicArithmetic_DedekindLFunctions_LandauTheorems_LFunctionConj
import Theorems.Thm_Deduction_LFunctionConjugation_hurwitz_conj_real

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex MeasureTheory Set Filter Topology
noncomputable section
open Deduction
open Deduction.LFunctionConjugation
open HurwitzZeta
namespace Deduction.LFunctionConjugation
theorem _root_.solution (a : UnitAddCircle) (s : ℂ) :
    hurwitzZeta a ((starRingEnd ℂ) s) = (starRingEnd ℂ) (hurwitzZeta a s) := by
  induction a using QuotientAddGroup.induction_on with
  | H b =>
    have hb : ((b : ℝ) : UnitAddCircle) = ((Int.fract b : ℝ) : UnitAddCircle) := by
      rw [QuotientAddGroup.eq]
      exact ⟨-⌊b⌋, by simp only [Int.fract, zsmul_eq_mul, mul_one, Int.cast_neg]; ring⟩
    rw [hb]
    exact hurwitz_conj_real ⟨Int.fract_nonneg b, (Int.fract_lt_one b).le⟩ s
end Deduction.LFunctionConjugation
