-- Prove2me | solution 1 for Formalism.GM.gammaIntegralityLemmas.aeval_int
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:33:44.041823+00:00
-- url     : https://prove2.me/submissions/76b72121-2137-442c-84e8-6d0befa4b90e

import Definitions.Def_Formalism_MahlerMeasure_GamInt
import Mathlib
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_GamInt
import Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_IVP_mul
import Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_IVP_sum
import Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_AllMono_mul
import Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_AllMono_sum
import Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_AllMono_pow
import Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_AllMono_prod
import Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_IsIntP_mul
import Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_IsIntP_sum
import Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_IsIntP_prod
import Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_IsIntP_pow
import Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_freezeSub_int
import Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_aeval_expand

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.gammaIntegralityLemmas
open MvPolynomial Finset Formalism.GM.M
variable {p : ℕ} [hp : Fact p.Prime]
variable {N r : ℕ}
namespace Formalism.GM.gammaIntegralityLemmas
theorem _root_.solution (LL : Letters (N + 1)) (ρ : Fin r)
    (f : MvPolynomial (Fin (N + 1) × Fin r) ℚ_[p]) (hf : ∀ μ, ‖coeff μ f‖ ≤ 1) :
    IsIntP (aeval (freezeSub p LL ρ) f) := by
  rw [aeval_expand]
  apply IsIntP.sum
  intro μ _
  exact (IsIntP.C (hf μ)).mul (IsIntP.prod _ _ (fun v _ => (freezeSub_int LL ρ v).pow _))
end Formalism.GM.gammaIntegralityLemmas
