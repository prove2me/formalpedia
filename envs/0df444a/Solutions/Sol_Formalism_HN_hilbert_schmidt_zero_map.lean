-- Prove2me | solution 1 for Formalism.HN.hilbert_schmidt_zero_map
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:41:25.969294+00:00
-- url     : https://prove2.me/submissions/b6dd33ba-f3ac-47b4-acc4-82102b4df2ae

import Definitions.Def_Formalism_HarderNarasimhan_StatementFrameF
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_FrameHermSharpB
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_FrameLinearAlgebraFirst
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_TheoremFSharp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField Finset Formalism.CorankShareLayerCake.FR
noncomputable section
open Formalism Formalism.HN
namespace Formalism.HN
theorem _root_.solution {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]
    (c : ℝ) : hs2 (frK c (0 : E →ₗ[ℂ] F) - LinearMap.id) = finrank ℂ E := by
  simp [hs2, frK, LinearMap.trace_id]
end Formalism.HN
