-- Prove2me | solution 1 for Formalism.DivisionValues.successive_minimum_log
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:51:18.725878+00:00
-- url     : https://prove2.me/submissions/6cc89e4f-206c-4db0-a314-eca67438a8b9

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_HeightBoundExactNorms
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ReductionThirdStepMean
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SlopeIneqMean
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_DescendedNorm
import Theorems.Thm_Formalism_DivisionValues_OperatorNormFrames_minOver_le
import Theorems.Thm_Formalism_DivisionValues_OperatorNormFrames_exists_minOver
import Theorems.Thm_Formalism_DivisionValues_OperatorNormFrames_le_minOver

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField
open scoped Matrix ComplexOrder InnerProductSpace
noncomputable section
open Formalism Formalism.DivisionValues
open OperatorNormFrames
open OperatorNormFrames
namespace Formalism.DivisionValues
theorem _root_.solution : SminLog := by
  unfold SminLog
  intro Ix J _ _ _ κ lam hκ hlam
  have hpos : ∀ p, 0 < ∏ j, lam j p := fun p => Finset.prod_pos fun j _ => hlam j p
  have hlog : ∀ p, Real.log (∏ j, lam j p) = ∑ j, Real.log (lam j p) := by
    intro p
    first
      | exact Real.log_prod fun j _ => (hlam j p).ne'
      | exact Real.log_prod _ _ fun j _ => (hlam j p).ne'
  obtain ⟨q, hq0⟩ := exists_minOver (fun p => ∏ j, lam j p)
  have hq : minOver (fun p => ∏ j, lam j p) = ∏ j, lam j q := hq0
  have hmin : ∀ p, ∏ j, lam j q ≤ ∏ j, lam j p := by
    intro p
    rw [← hq]
    exact minOver_le _ p
  refine ⟨?_, fun p => ?_, ⟨q, by rw [hq]⟩, ?_⟩
  · rw [hq]
    exact mul_pos hκ (hpos q)
  · exact mul_le_mul_of_nonneg_left (minOver_le _ p) hκ.le
  · rw [hq, Real.log_mul hκ.ne' (hpos q).ne', hlog q]
    congr 1
    apply le_antisymm
    · apply le_minOver
      intro p
      show ∑ j, Real.log (lam j q) ≤ ∑ j, Real.log (lam j p)
      rw [← hlog q, ← hlog p]
      exact Real.log_le_log (hpos q) (hmin p)
    · exact minOver_le _ q
end Formalism.DivisionValues
