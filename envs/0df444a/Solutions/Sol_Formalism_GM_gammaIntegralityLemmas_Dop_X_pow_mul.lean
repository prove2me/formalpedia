-- Prove2me | solution 1 for Formalism.GM.gammaIntegralityLemmas.Dop_X_pow_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:34:28.24593+00:00
-- url     : https://prove2.me/submissions/58625edb-1e1b-40ab-90ee-d4631b4bb4ba

import Definitions.Def_Formalism_MahlerMeasure_GamInt
import Mathlib
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_GamInt
import Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_Dop_apply
import Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_pderiv_X_pow_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.gammaIntegralityLemmas
open MvPolynomial Finset
variable {p : ℕ} [hp : Fact p.Prime]
variable {σ : Type} [DecidableEq σ]
namespace Formalism.GM.gammaIntegralityLemmas
theorem _root_.solution (u v y : σ) (huy : u ≠ y) (hvy : v ≠ y) (m : ℕ) (G : MvPolynomial σ ℚ_[p]) :
    Dop u v (X y ^ m * G) = X y ^ m * Dop u v G := by
  rw [Dop_apply, Dop_apply, pderiv_X_pow_mul v y hvy, pderiv_X_pow_mul u y huy]
end Formalism.GM.gammaIntegralityLemmas
