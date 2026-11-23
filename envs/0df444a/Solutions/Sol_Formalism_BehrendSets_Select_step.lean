-- Prove2me | solution 1 for Formalism.BehrendSets.Select.step
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:12:40.744531+00:00
-- url     : https://prove2.me/submissions/f75fcc51-924d-433b-92cd-28517e697fb3

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
theorem _root_.solution (X : Finset α) (δ : ℝ) {a : α} (ha : a ∉ X) (g : Finset α → ℝ) :
    ∑ T ∈ (insert a X).powerset, wt (insert a X) δ T * g T =
      ∑ T ∈ X.powerset, wt X δ T * ((1 - δ) * g T + δ * g (insert a T)) := by
  rw [Finset.sum_powerset_insert ha, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro T hT
  have haT : a ∉ T := fun h => ha (Finset.mem_powerset.1 hT h)
  have haXT : a ∉ X \ T := fun h => ha (Finset.mem_sdiff.1 h).1
  have e1 : wt (insert a X) δ T = wt X δ T * (1 - δ) := by
    unfold wt
    rw [Finset.insert_sdiff_of_notMem X haT, Finset.card_insert_of_notMem haXT, pow_succ]
    ring
  have e2 : wt (insert a X) δ (insert a T) = wt X δ T * δ := by
    unfold wt
    rw [Finset.insert_sdiff_insert, Finset.sdiff_insert_of_notMem ha,
      Finset.card_insert_of_notMem haT, pow_succ]
    ring
  rw [e1, e2]
  ring
end Formalism.BehrendSets.Select
