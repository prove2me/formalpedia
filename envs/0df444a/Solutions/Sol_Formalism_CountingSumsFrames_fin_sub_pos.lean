-- Prove2me | solution 1 for Formalism.CountingSumsFrames.fin_sub_pos
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:07:13.179619+00:00
-- url     : https://prove2.me/submissions/2e60e097-640d-40bf-8386-dafe516a91f4

import Definitions.Def_Formalism_PolynomialDimension_DigitClassSize
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_WeylDimPosOfAntitone

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped BigOperators
open Finset
open Formalism Formalism.CountingSumsFrames
namespace Formalism.CountingSumsFrames
theorem _root_.solution (m : ℕ) (j : Fin m) : 0 < (m : ℝ) - ((j : ℕ) : ℝ) := by
  have : ((j : ℕ) : ℝ) < (m : ℝ) := by exact_mod_cast j.isLt
  linarith
end Formalism.CountingSumsFrames
