-- Prove2me | solution 1 for Bl.general_b_fact_left_extra.goal1
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:12:23.5518+00:00
-- url     : https://prove2.me/submissions/4890846a-5717-45f6-84ab-adb37e892849

import Mathlib
import Definitions.Def_Lemmata_GeneralBFactLeftExtra_Imports

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
open Bl Bl.general_b_fact_left_extra
variable {K : Type*} [Field K] [NumberField K]
namespace Bl.general_b_fact_left_extra
theorem _root_.solution {ι : Type*} (w : FinitePlace K) (t : Finset ι) (a : ι → K) {M : ℝ}
    (hM : 0 ≤ M) (h : ∀ i ∈ t, w (a i) ≤ M) : w (∑ i ∈ t, a i) ≤ M := by
  classical
  induction t using Finset.induction_on with
  | empty => simpa using hM
  | insert j s hj ih =>
    rw [Finset.sum_insert hj]
    refine (FinitePlace.add_le w _ _).trans (max_le ?_ ?_)
    · exact h j (Finset.mem_insert_self j s)
    · exact ih (fun i hi => h i (Finset.mem_insert_of_mem hi))
end Bl.general_b_fact_left_extra
