-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.GelfandTsetlinBases.SpanImageLemmas.basis
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T12:07:58.029454+00:00
-- url     : https://prove2.me/submissions/1df662b4-be41-4256-81d9-645fa2a6cd4b

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_CorA3primeB
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_PathBasisOfCount
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_LeIffLtColHeight
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_MemSpanImageIff

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
open Formalism.InvariantFactorPaths.GelfandTsetlinBases.SpanImageLemmas
variable {n N : ℕ} {isVec : ℕ → Bool} {B : ℕ → ℕ}
namespace Formalism.InvariantFactorPaths.GelfandTsetlinBases.SpanImageLemmas
theorem _root_.solution (hc : CountPAll) (h2 : PathBasisOfCount) (R : Type) [CommRing R] (n N : ℕ) (isVec : ℕ → Bool) (B : ℕ → ℕ) :
    LinearIndependent R (psiFam R n N isVec B) ∧
      Submodule.span R (Set.range (psiFam R n N isVec B)) = polB R n N B :=
  h2 n N isVec B (hc n N isVec B) R
end Formalism.InvariantFactorPaths.GelfandTsetlinBases.SpanImageLemmas
