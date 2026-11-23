-- Prove2me | solution 1 for Formalism.CountingSumsFrames.harmonic_level_count
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:51:43.101084+00:00
-- url     : https://prove2.me/submissions/e39b4d5f-ef09-4e5a-9e18-8d63644b823f

import Definitions.Def_Formalism_PolynomialDimension_DigitClassSize
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_HarmonicLevelCountRec
import Theorems.Thm_Formalism_CountingSumsFrames_harmonic_level_count_rec

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
theorem _root_.solution : LevelCount :=
  fun k' A B => harmonic_level_count_rec k' A B
end Formalism.CountingSumsFrames
