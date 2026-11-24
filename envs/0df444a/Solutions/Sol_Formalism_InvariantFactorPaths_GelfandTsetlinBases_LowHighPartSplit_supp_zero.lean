-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.GelfandTsetlinBases.LowHighPartSplit.supp_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T09:47:57.82195+00:00
-- url     : https://prove2.me/submissions/afe15650-1889-4b2d-b965-24b50c90f5b9

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_CorA3primeB
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_ExistsSuppOfEvalNe
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_IndexWeightsDominance
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_FactSplit

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
open Formalism.InvariantFactorPaths.GelfandTsetlinBases.LowHighPartSplit
variable {n : ℕ}
namespace Formalism.InvariantFactorPaths.GelfandTsetlinBases.LowHighPartSplit
theorem _root_.solution {σ L : Type*} [CommRing L] {Lo : Set σ} {P : MvPolynomial σ L} (hP : P ∈ supported L Lo)
    {e : σ →₀ ℕ} (he : e ∈ P.support) {x : σ} (hx : x ∉ Lo) : e x = 0 := by
  by_contra h
  apply hx
  exact (mem_supported.mp hP) (Finset.mem_coe.mpr ((mem_vars x).mpr ⟨e, he, Finsupp.mem_support_iff.mpr h⟩))
end Formalism.InvariantFactorPaths.GelfandTsetlinBases.LowHighPartSplit
