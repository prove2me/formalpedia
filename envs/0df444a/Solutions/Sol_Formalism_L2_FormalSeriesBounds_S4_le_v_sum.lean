-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.S4.le_v_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T09:57:04.187582+00:00
-- url     : https://prove2.me/submissions/07a62396-34f7-4c79-b4fd-a2b1be812275

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_ExistsStrictMonoMinor

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds Formalism.L2.FormalSeriesBounds.S4
variable {R : Type*} [CommRing R]
namespace Formalism.L2.FormalSeriesBounds.S4
theorem _root_.solution (v : AddValuation R (WithTop ℝ)) {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (f : ι → R) (g : WithTop ℝ) (hg : ∀ i ∈ s, g ≤ v (f i)) : g ≤ v (∑ i ∈ s, f i) := by
  revert hg
  refine Finset.induction_on s (fun _ => by simp) ?_
  intro i s hi ih hg
  rw [Finset.sum_insert hi]
  exact le_trans (le_min (hg i (Finset.mem_insert_self i s))
    (ih fun j hj => hg j (Finset.mem_insert_of_mem hj))) (v.map_add _ _)
end Formalism.L2.FormalSeriesBounds.S4
