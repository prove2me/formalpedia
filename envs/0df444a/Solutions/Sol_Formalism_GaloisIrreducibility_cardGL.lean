-- Prove2me | solution 1 for Formalism.GaloisIrreducibility.cardGL
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T16:58:45.405432+00:00
-- url     : https://prove2.me/submissions/4b614178-9faa-43ae-b6e7-4708b73b2202

import Definitions.Def_Formalism_GaloisIrreducibility_GaloisIrreducibilityProofs_OrbitSubSum
import Definitions.Def_Formalism_GaloisIrreducibility_GaloisIrreducibilityProofs_RestrictRoots
import Definitions.Def_Formalism_GaloisIrreducibility_GaloisIrreducibilityProofs_LemmaAOf
import Definitions.Def_Formalism_GaloisIrreducibility_GaloisIrreducibilityProofs_IrredOf
import Definitions.Def_Formalism_GaloisIrreducibility_GaloisIrreducibilityProofs_PermSubSumInv
import Definitions.Def_Formalism_GaloisIrreducibility_GaloisIrreducibilityProofs_ResiduesLe
import Definitions.Def_Formalism_GaloisIrreducibility_GaloisIrreducibilityProofs_FewLargeParts
import Definitions.Def_Formalism_GaloisIrreducibility_GaloisIrreducibilityProofs_BlockBoundOfOrbits
import Definitions.Def_Formalism_GaloisIrreducibility_GaloisIrreducibilityProofs_OneNonUnit
import Definitions.Def_Formalism_GaloisIrreducibility_GaloisIrreducibilityProofs_PowerPCycle
import Definitions.Def_Formalism_GaloisIrreducibility_GaloisIrreducibilityProofs_AltNotSolvable
import Definitions.Def_Formalism_GaloisIrreducibility_GaloisIrreducibilityProofs_NoSolvableOf
import Definitions.Def_Formalism_GaloisIrreducibility_GaloisIrreducibilityProofs_PrimitiveOfPCycle
import Definitions.Def_Formalism_GaloisIrreducibility_GaloisIrreducibilityProofs_JordanPrime
import Definitions.Def_Formalism_GaloisIrreducibility_NoSolvableTransitive

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GaloisIrreducibility
namespace Formalism.GaloisIrreducibility
theorem _root_.solution : CardGL := by
  intro K _ _ _ N
  have hinj : Function.Injective
      (fun g : GL (Fin N) K => fun i j : Fin N => (g : Matrix (Fin N) (Fin N) K) i j) := by
    intro g h hgh
    apply Units.ext
    exact Matrix.ext fun i j => congrFun (congrFun hgh i) j
  refine le_trans (Fintype.card_le_of_injective _ hinj) (le_of_eq ?_)
  rw [Fintype.card_fun, Fintype.card_fun, Fintype.card_fin, ← pow_mul, sq]
end Formalism.GaloisIrreducibility
