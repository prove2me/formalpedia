-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.norm_placeEmbedding_sub
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:57:45.406422+00:00
-- url     : https://prove2.me/submissions/27a738d8-e6be-4bd8-8f2e-bd7e83f2aa90

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
theorem _root_.solution (E : Type) [Field E] (x y : E) (w : InfinitePlace E) :
    ‖infinitePlaceEmbedding E x w - infinitePlaceEmbedding E y w‖ = w (x - y) := by
  rw [← InfinitePlace.norm_embedding_eq w (x - y), map_sub]; rfl
end Formalism.HermitianLatticeCounting.P
