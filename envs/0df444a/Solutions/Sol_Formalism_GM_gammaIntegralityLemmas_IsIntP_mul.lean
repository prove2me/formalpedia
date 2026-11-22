-- Prove2me | solution 1 for Formalism.GM.gammaIntegralityLemmas.IsIntP.mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:27:52.481369+00:00
-- url     : https://prove2.me/submissions/0de9bb66-a836-4af4-b075-11712f786e53

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
theorem _root_.solution {P P' : MvPolynomial σ ℚ_[p]} (h : IsIntP P) (h' : IsIntP P') : IsIntP (P * P') := by
  intro β
  rw [coeff_mul]
  apply norm_sum_le_one
  intro x _
  rw [norm_mul]
  exact mul_le_one₀ (h _) (norm_nonneg _) (h' _)
end IsIntP
end Formalism.GM.gammaIntegralityLemmas
