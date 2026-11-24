-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.norm_placeEmbedding
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:57:45.155302+00:00
-- url     : https://prove2.me/submissions/07c3fbda-880a-4bae-9b16-ffc52548e169

import Definitions.Def_Formalism_FlagUnipotentLattices_UnipotentStabiliserCharacterisation
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_BlockMinorSumCounterexample

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
open Finset Real MeasureTheory NumberField Formalism.HermitianLatticeCounting.ExpansionTerms
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution (E : Type) [Field E] (x : E) (w : InfinitePlace E) : ‖infinitePlaceEmbedding E x w‖ = w x :=
  InfinitePlace.norm_embedding_eq w x
end Formalism.HermitianLatticeCounting.P
