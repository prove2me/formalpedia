-- Prove2me | solution 1 for Formalism.CountingSumsFrames.compP_true
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:41:28.676665+00:00
-- url     : https://prove2.me/submissions/9f126e3a-0e89-4146-abec-dbc979a1757d

import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_TheoremM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FockBlocks
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_RemoveS
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_PartnerM
import Theorems.Thm_Formalism_CountingSumsFrames_coeff_compP

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.CountingSumsFrames
open Formalism.GM Formalism.GM.TM M MvPolynomial Finset
variable {K σ : Type} [Field K]
namespace Formalism.CountingSumsFrames
theorem _root_.solution (x : MvPolynomial σ K) : compP (fun _ => True) x = x := by
  ext m
  simp [coeff_compP]
end Formalism.CountingSumsFrames
