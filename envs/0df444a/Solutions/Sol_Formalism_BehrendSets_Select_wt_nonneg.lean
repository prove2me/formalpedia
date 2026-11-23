-- Prove2me | solution 1 for Formalism.BehrendSets.Select.wt_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:12:40.808061+00:00
-- url     : https://prove2.me/submissions/e7253311-15cb-4f6d-90f6-55c6404e182a

import Mathlib
import Definitions.Def_Formalism_BehrendSets_Statement
import Definitions.Def_Formalism_BehrendSets_BehrendVariance_Select

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
open Formalism Formalism.BehrendSets Formalism.BehrendSets.Select
variable {α : Type} [DecidableEq α]
namespace Formalism.BehrendSets.Select
theorem _root_.solution (X : Finset α) {δ : ℝ} (h0 : 0 ≤ δ) (h1 : δ ≤ 1) (T : Finset α) :
    0 ≤ wt X δ T :=
  mul_nonneg (pow_nonneg h0 _) (pow_nonneg (by linarith) _)
end Formalism.BehrendSets.Select
