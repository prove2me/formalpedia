-- Prove2me | solution 1 for Formalism.CountingSumsFrames.dimPol_mul_deg_real
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T16:28:30.708783+00:00
-- url     : https://prove2.me/submissions/c11bb52f-8ae1-4964-a77d-80cb5115425a

import Definitions.Def_Formalism_PolynomialDimension_DigitClassSize
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_HarmonicLevelCountRec
import Theorems.Thm_Formalism_CountingSumsFrames_dimPol_mul_deg

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
theorem _root_.solution (k' b : ℕ) :
    (dimPol k' b : ℝ) * ((b : ℝ) + 1 + k') = (dimPol k' (b + 1) : ℝ) * ((b : ℝ) + 1) := by
  exact_mod_cast dimPol_mul_deg k' b
end Formalism.CountingSumsFrames
