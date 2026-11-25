-- Prove2me | solution 1 for Formalism.TruncatedSeriesCounting.TruncatedSeriesCountingIdentities.DetPolyApp.S1_mem_OmF
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:22:41.09394+00:00
-- url     : https://prove2.me/submissions/8509016d-38a3-40ec-add7-299f28dd8a84

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
theorem _root_.solution {T : Subalgebra O (Xs → O)} {m : ℕ} {f : Xs → MvPolynomial (Fin m) K} :
    f ∈ S1 T m ↔ ∀ α, FromT T (fun x => (f x).coeff α) := Iff.rfl
end Formalism.TruncatedSeriesCounting.TruncatedSeriesCountingIdentities.DetPolyApp
