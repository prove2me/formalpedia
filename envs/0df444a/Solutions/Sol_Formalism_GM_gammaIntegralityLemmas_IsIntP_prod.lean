-- Prove2me | solution 1 for Formalism.GM.gammaIntegralityLemmas.IsIntP.prod
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:53:50.622809+00:00
-- url     : https://prove2.me/submissions/46d9d734-0ae2-4719-9dbd-34a910142b4e

import Definitions.Def_Formalism_MahlerMeasure_GamInt
import Mathlib
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_GamInt
import Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_IVP_mul
import Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_AllMono_mul
import Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_AllMono_one
import Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_IsIntP_mul
import Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_IsIntP_one

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
namespace IsIntP
theorem _root_.solution {ι : Type} (s : Finset ι) (P : ι → MvPolynomial σ ℚ_[p]) (h : ∀ i ∈ s, IsIntP (P i)) :
    IsIntP (∏ i ∈ s, P i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using IsIntP.one (p := p) (σ := σ)
  | insert a s ha ih =>
    rw [prod_insert ha]; exact (h a (mem_insert_self _ _)).mul (ih (fun i hi => h i (mem_insert_of_mem hi)))
end IsIntP
end Formalism.GM.gammaIntegralityLemmas
