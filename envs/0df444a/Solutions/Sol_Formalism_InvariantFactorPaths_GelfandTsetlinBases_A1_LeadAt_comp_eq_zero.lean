-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.GelfandTsetlinBases.A1.LeadAt.comp_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:57:24.191845+00:00
-- url     : https://prove2.me/submissions/d501688e-fbf2-416e-beae-db61705da69e

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
theorem _root_.solution {w : σ → M} {γ γ' : M} {f t : MvPolynomial σ R} (hf : LeadAt w γ f t)
    (h : γ < γ') : weightedHomogeneousComponent w γ' f = 0 := by
  ext e
  rw [coeff_weightedHomogeneousComponent, coeff_zero]
  split_ifs with he
  · by_contra hne
    have := hf.1 e (mem_support_iff.mpr hne)
    rw [he] at this
    exact absurd this (not_le.mpr h)
  · rfl
end LeadAt
end Formalism.InvariantFactorPaths.GelfandTsetlinBases.A1
