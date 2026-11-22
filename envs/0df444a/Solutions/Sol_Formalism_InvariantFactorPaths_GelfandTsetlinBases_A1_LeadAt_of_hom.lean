-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.GelfandTsetlinBases.A1.LeadAt.of_hom
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:38:21.811931+00:00
-- url     : https://prove2.me/submissions/055f5ed1-25b9-4412-8e71-3cf17f0aa509

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_StatementA
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_LeIffLtColHeight
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_IsWeightedHomogeneousZeroStripPathWord

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset MvPolynomial
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.GelfandTsetlinBases
open Formalism.InvariantFactorPaths.GelfandTsetlinBases.A1
variable {σ R M : Type*} [CommRing R] [AddCommMonoid M] [LinearOrder M] [IsOrderedCancelAddMonoid M]
namespace Formalism.InvariantFactorPaths.GelfandTsetlinBases.A1
namespace LeadAt
theorem _root_.solution {w : σ → M} {γ : M} {f : MvPolynomial σ R} (hf : IsWeightedHomogeneous w f γ) :
    LeadAt w γ f f := by
  refine ⟨fun e he => le_of_eq (hf (mem_support_iff.mp he)), ?_⟩
  ext e
  rw [coeff_weightedHomogeneousComponent]
  split_ifs with h
  · rfl
  · by_contra hne
    exact h (hf (Ne.symm hne))
end LeadAt
end Formalism.InvariantFactorPaths.GelfandTsetlinBases.A1
