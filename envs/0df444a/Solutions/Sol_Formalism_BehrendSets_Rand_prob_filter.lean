-- Prove2me | solution 1 for Formalism.BehrendSets.Rand.prob_filter
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:41:45.213064+00:00
-- url     : https://prove2.me/submissions/38541821-bd4d-4b4f-95f9-f41312e419cf

import Mathlib
import Definitions.Def_Formalism_BehrendSets_Statement
import Definitions.Def_Formalism_BehrendSets_BehrendVariance_ProbEqSumIte
import Theorems.Thm_Formalism_BehrendSets_Rand_prob_eq_sum_ite

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open Formalism Formalism.BehrendSets Formalism.BehrendSets.Rand
variable {α : Type} [DecidableEq α]
namespace Formalism.BehrendSets.Rand
theorem _root_.solution (X : Finset α) (δ : ℝ) (P : Finset α → Prop) [DecidablePred P] :
    prob X δ P = ∑ T ∈ X.powerset.filter P, wt X δ T := by
  rw [prob_eq_sum_ite, Finset.sum_filter]
end Formalism.BehrendSets.Rand
