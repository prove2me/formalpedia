-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.GelfandTsetlinBases.DominanceOrderLemmas.domLe_trans
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T09:47:20.725523+00:00
-- url     : https://prove2.me/submissions/33a1dc72-a4a6-4a1e-8062-ae783896672c

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_CorA3primeB
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_LemmaA2indepOf
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_JacobiMinorProof
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_GenSpace
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_LeIffLtColHeight
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_GoodWOfWeight

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
open Formalism.InvariantFactorPaths.GelfandTsetlinBases.DominanceOrderLemmas
namespace Formalism.InvariantFactorPaths.GelfandTsetlinBases.DominanceOrderLemmas
theorem _root_.solution {n : ℕ} {a b c : Fin n → ℤ} (h1 : DomLe a b) (h2 : DomLe b c) : DomLe a c :=
  ⟨h1.1.trans h2.1, fun j => (h1.2 j).trans (h2.2 j)⟩
end Formalism.InvariantFactorPaths.GelfandTsetlinBases.DominanceOrderLemmas
