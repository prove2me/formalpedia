-- Prove2me | solution 1 for Formalism.REAL.signMatch_mul_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:35:59.017928+00:00
-- url     : https://prove2.me/submissions/8db60018-7419-480d-b988-20ce44bc5560

import Definitions.Def_Formalism_RealPlaceAnalysis_FockPairGl
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ProdFactorialSupportSubSingle

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
open Formalism Formalism.REAL
variable {M n' : ℕ}
namespace Formalism.REAL
theorem _root_.solution (ε : Fin M → Bool) (ε' : Fin n' → Bool) (i : Fin M) (a b : Fin n') :
    ((if sgnv ε ε' i b then 1 else -1 : ℂ) * (if sgnv ε ε' i a then 1 else -1)) =
      ((sgn ε' a b : ℝ) : ℂ) := by
  unfold sgnv sgn
  generalize ε i = x; generalize ε' a = y; generalize ε' b = z
  cases x <;> cases y <;> cases z <;> norm_num
end Formalism.REAL
