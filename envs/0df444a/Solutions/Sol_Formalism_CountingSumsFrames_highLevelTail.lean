-- Prove2me | solution 1 for Formalism.CountingSumsFrames.highLevelTail
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:58:12.968875+00:00
-- url     : https://prove2.me/submissions/d543a97b-7454-4823-ba55-0aeee7d112e8

import Definitions.Def_Formalism_PolynomialDimension_DigitClassSize
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_HarmonicLevelCountRec
import Theorems.Thm_Formalism_CountingSumsFrames_sum_Icc_dimHar
import Theorems.Thm_Formalism_CountingSumsFrames_tail_bound

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
open Finset
open Formalism Formalism.CountingSumsFrames
namespace Formalism.CountingSumsFrames
theorem _root_.solution : LevelTail :=
  fun k' A B J hJ => ⟨sum_Icc_dimHar k' A B J hJ, tail_bound k' A B J hJ⟩
end Formalism.CountingSumsFrames
