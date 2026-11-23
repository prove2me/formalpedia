-- Prove2me | solution 1 for Formalism.GM.FrozenVariableLemmas.isWH_X_fst
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:44:38.103739+00:00
-- url     : https://prove2.me/submissions/32a9c825-058d-4a10-9a79-11756061b6ec

import Definitions.Def_Formalism_MahlerMeasure_IsFrozenInv
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeInto

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.FrozenVariableLemmas
open MvPolynomial Finset
namespace Formalism.GM.FrozenVariableLemmas
theorem _root_.solution {M r : ℕ} {R : Type} [CommSemiring R] (g : Fin M → ℕ) (b : Fin M) (c : Fin r) :
    IsWeightedHomogeneous (fun x : Fin M × Fin r => g x.1) (X (b, c) : MvPolynomial _ R) (g b) :=
  isWeightedHomogeneous_X R _ (b, c)
end Formalism.GM.FrozenVariableLemmas
