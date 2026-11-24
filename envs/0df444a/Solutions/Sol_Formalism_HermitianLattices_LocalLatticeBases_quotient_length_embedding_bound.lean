-- Prove2me | solution 1 for Formalism.HermitianLattices.LocalLatticeBases.quotient_length_embedding_bound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:42:49.364807+00:00
-- url     : https://prove2.me/submissions/9b2f5dc6-d1f1-4aa1-bf81-d259f52a9dfe

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_FourierTransformKernelSurjective
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_FourierCommutesHeckeScalar

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.LocalLatticeBases
open Finset
namespace Formalism.HermitianLattices.LocalLatticeBases
theorem _root_.solution : QuotientLengthEmbeddingBound := by
  intro R _ M _ _ A N
  apply Module.length_le_of_injective (Submodule.mapQ (N.comap A.subtype) N A.subtype le_rfl)
  rw [← LinearMap.ker_eq_bot, Submodule.ker_mapQ]
  simp
end Formalism.HermitianLattices.LocalLatticeBases
