-- Prove2me | solution 1 for Formalism.GM.gammaIntegralityLemmas.freezeSub_int
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:25:23.964015+00:00
-- url     : https://prove2.me/submissions/aeee46b3-bf30-4304-b4b1-293fe8a7b254

import Definitions.Def_Formalism_MahlerMeasure_GamInt
import Mathlib
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_GamInt
import Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_IVP_mul
import Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_IVP_sum
import Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_AllMono_mul
import Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_AllMono_sum
import Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_AllMono_sub
import Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_IsIntP_mul
import Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_IsIntP_sub
import Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_IsIntP_sum

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
theorem _root_.solution (LL : Letters (N + 1)) (ρ : Fin r) (v : Fin (N + 1) × Fin r) :
    IsIntP (freezeSub p LL ρ v) := by
  obtain ⟨i, c⟩ := v
  simp only [freezeSub]
  split_ifs
  · exact IsIntP.sum _ _ (fun _ _ => (IsIntP.X _).mul (IsIntP.X _))
  · exact (IsIntP.X _).mul (IsIntP.X _)
  · exact (IsIntP.X _).mul (IsIntP.X _)
  · exact ((IsIntP.X _).mul (IsIntP.X _)).sub ((IsIntP.X _).mul (IsIntP.X _))
end Formalism.GM.gammaIntegralityLemmas
