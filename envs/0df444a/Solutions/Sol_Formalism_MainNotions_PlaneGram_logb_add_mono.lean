-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.logb_add_mono
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T11:07:47.092673+00:00
-- url     : https://prove2.me/submissions/92bac9c3-996e-4027-9601-49e2e17bb449

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_MemPolKIff
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_CgeZeroIffIntegral

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Finset
open Formalism Formalism.MainNotions Formalism.MainNotions.PlaneGram
variable {K : Type} [Field K] (v : AddValuation K (WithTop ℚ))
namespace Formalism.MainNotions.PlaneGram
theorem _root_.solution {p : ℕ} (hp : 2 ≤ p) (r : ℕ) {a b : ℕ} (h : 1 ≤ a + r) (hab : a ≤ b) :
    Real.logb p ((a : ℝ) + r) ≤ Real.logb p ((b : ℝ) + r) := by
  apply Real.logb_le_logb_of_le
  · exact_mod_cast (by omega : 1 < p)
  · have : (1 : ℝ) ≤ a + r := by exact_mod_cast h
    linarith
  · have : (a : ℝ) ≤ b := by exact_mod_cast hab
    linarith
end Formalism.MainNotions.PlaneGram
