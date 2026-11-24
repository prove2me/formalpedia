-- Prove2me | solution 1 for Formalism.GM.GammaExpansion.pow_Dp_X_pow
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:20:53.096424+00:00
-- url     : https://prove2.me/submissions/96cca58e-a04c-4f8e-96f6-0bd74ed9eac0

import Definitions.Def_Formalism_MahlerMeasure_HasOrder
import Definitions.Def_Formalism_MahlerMeasure_FinalM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeInto
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_GamDeg
import Theorems.Thm_Formalism_GM_GammaExpansion_pow_Dp_monomial

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.GammaExpansion
open MvPolynomial Finset
variable {R σ : Type} [CommSemiring R]
namespace Formalism.GM.GammaExpansion
theorem _root_.solution (v : σ) (m t : ℕ) :
    (Dp v ^ t) (X v ^ m : MvPolynomial σ R) = m.descFactorial t • X v ^ (m - t) := by
  rw [X_pow_eq_monomial, pow_Dp_monomial, Finsupp.single_eq_same, ← Finsupp.single_tsub,
    X_pow_eq_monomial, one_mul, smul_monomial, nsmul_eq_mul, mul_one]
end Formalism.GM.GammaExpansion
