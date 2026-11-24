-- Prove2me | solution 1 for Formalism.REAL.fischerInner_oscillatorRaise
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:34:58.738819+00:00
-- url     : https://prove2.me/submissions/e70afa4e-a6de-428d-85a4-40a304b4a710

import Definitions.Def_Formalism_RealPlaceAnalysis_FockPairGl
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ProdFactorialSupportSubSingle
import Theorems.Thm_Formalism_REAL_fischerInner_neg_left
import Theorems.Thm_Formalism_REAL_fischerInner_pderiv_left
import Theorems.Thm_Formalism_REAL_fischerInner_X_mul_left

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
theorem _root_.solution (ε : Fin M → Bool) (ε' : Fin n' → Bool) (i : Fin M) (a : Fin n')
    (f g : MvPolynomial (Fin M × Fin n') ℂ) :
    fockF (bpl ε ε' i a f) g = (if sgnv ε ε' i a then 1 else -1) * fockF f (bop ε ε' i a g) := by
  unfold bop bpl
  split_ifs with h
  · simp only [LinearMap.mulLeft_apply, Derivation.coeFn_coe, one_mul]
    exact fischerInner_X_mul_left _ f g
  · simp only [LinearMap.mulLeft_apply, LinearMap.neg_apply, Derivation.coeFn_coe, fischerInner_neg_left]
    rw [fischerInner_pderiv_left]; ring
end Formalism.REAL
