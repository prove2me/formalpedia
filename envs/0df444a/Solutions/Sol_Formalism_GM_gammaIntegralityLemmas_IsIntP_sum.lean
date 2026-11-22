-- Prove2me | solution 1 for Formalism.GM.gammaIntegralityLemmas.IsIntP.sum
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:27:52.425802+00:00
-- url     : https://prove2.me/submissions/48edb37d-0f1d-48df-bb45-8b845d2fa52b

import Definitions.Def_Formalism_MahlerMeasure_GamInt
import Mathlib
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_GamInt
import Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_norm_sum_le_one

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
    IsIntP (∑ i ∈ s, P i) := by
  intro β; rw [coeff_sum]; exact norm_sum_le_one _ _ (fun i hi => h i hi β)
end IsIntP
end Formalism.GM.gammaIntegralityLemmas
