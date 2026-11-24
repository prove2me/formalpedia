-- Prove2me | solution 1 for Formalism.TruncatedSeriesCounting.TruncatedSeriesCountingIdentities.DetPolyApp.mem_mainNotions_iff_fromT
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T11:37:25.965259+00:00
-- url     : https://prove2.me/submissions/5f7cb889-d994-4972-ab0d-0ede543120e0

import Definitions.Def_Formalism_TruncatedSeriesCounting_LemmaDetPoly
import Definitions.Def_Formalism_TruncatedSeriesCounting_TruncatedSeriesProofs_LemmaDetPoly

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Classical Polynomial
noncomputable section
open Formalism Formalism.TruncatedSeriesCounting Formalism.TruncatedSeriesCounting.TruncatedSeriesCountingIdentities Formalism.TruncatedSeriesCounting.TruncatedSeriesCountingIdentities.DetPolyApp
open DetPolyCore
variable {O K Xs : Type*} [CommRing O] [CommRing K] [Algebra O K]
namespace Formalism.TruncatedSeriesCounting.TruncatedSeriesCountingIdentities.DetPolyApp
theorem _root_.solution {T : Subalgebra O (Xs → O)} {f : Xs → K} : f ∈ MainNotions T ↔ FromT T f := Iff.rfl
end Formalism.TruncatedSeriesCounting.TruncatedSeriesCountingIdentities.DetPolyApp
