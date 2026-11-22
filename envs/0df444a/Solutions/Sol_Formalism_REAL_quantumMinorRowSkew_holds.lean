-- Prove2me | solution 1 for Formalism.REAL.quantumMinorRowSkew_holds
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T19:39:16.236249+00:00
-- url     : https://prove2.me/submissions/2af96c5f-e64a-4935-bc01-4dfe84c9660d

import Definitions.Def_Formalism_RealPlaceAnalysis_StatementE
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_QuantumDetHighestWeightHolds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open Formalism Formalism.REAL
namespace Formalism.REAL
theorem _root_.solution : QSkewRow := by
  intro A _ _ n t E a b τ u
  unfold qminor
  rw [Finset.mul_sum]
  refine Fintype.sum_equiv (Equiv.mulLeft τ) _ _ (fun σ => ?_)
  simp only [Equiv.coe_mulLeft]
  have hs : ((Equiv.Perm.sign τ : ℤ) : A) * ((Equiv.Perm.sign (τ * σ) : ℤ) : A) =
      ((Equiv.Perm.sign σ : ℤ) : A) := by
    rw [← Int.cast_mul, Equiv.Perm.sign_mul, ← Units.val_mul, ← mul_assoc, Int.units_mul_self, one_mul]
  rw [← mul_assoc, hs]
  rfl
end Formalism.REAL
