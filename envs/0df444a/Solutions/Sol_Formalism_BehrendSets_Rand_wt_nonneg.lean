-- Prove2me | solution 1 for Formalism.BehrendSets.Rand.wt_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:41:24.850215+00:00
-- url     : https://prove2.me/submissions/d513be92-7fcc-465d-9db5-d9e757225ec3

import Mathlib
import Definitions.Def_Formalism_BehrendSets_Statement
import Definitions.Def_Formalism_BehrendSets_BehrendVariance_ProbEqSumIte

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
theorem _root_.solution (X T : Finset α) {δ : ℝ} (h0 : 0 ≤ δ) (h1 : δ ≤ 1) : 0 ≤ wt X δ T := by
  unfold wt
  exact mul_nonneg (pow_nonneg h0 _) (pow_nonneg (sub_nonneg.mpr h1) _)
end Formalism.BehrendSets.Rand
