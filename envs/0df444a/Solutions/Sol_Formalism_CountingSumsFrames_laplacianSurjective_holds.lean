-- Prove2me | solution 1 for Formalism.CountingSumsFrames.laplacianSurjective_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:27:21.475485+00:00
-- url     : https://prove2.me/submissions/a97142e4-235f-4c9e-891c-a4ecb3b98aca

import Definitions.Def_Formalism_PolynomialDimension_StatementHar
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_HarmonicDecompositionHolds
import Theorems.Thm_Formalism_CountingSumsFrames_Har2_exists_laplacian_eq

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
open Formalism Formalism.CountingSumsFrames
open Har2
namespace Formalism.CountingSumsFrames
theorem _root_.solution : CtrSurj := by
  unfold CtrSurj
  intro K _ _ k A B hk g hg
  exact exists_laplacian_eq hk hg
end Formalism.CountingSumsFrames
