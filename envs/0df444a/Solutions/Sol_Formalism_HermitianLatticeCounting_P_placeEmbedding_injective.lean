-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.placeEmbedding_injective
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:04:14.532805+00:00
-- url     : https://prove2.me/submissions/95f029d2-209f-44be-96e1-891889562f69

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
theorem _root_.solution (E : Type) [Field E] [NumberField E] : Function.Injective (infinitePlaceEmbedding E) := by
  intro x y h
  obtain ⟨w⟩ := (inferInstance : Nonempty (InfinitePlace E))
  exact w.embedding.injective (congrFun h w)
end Formalism.HermitianLatticeCounting.P
