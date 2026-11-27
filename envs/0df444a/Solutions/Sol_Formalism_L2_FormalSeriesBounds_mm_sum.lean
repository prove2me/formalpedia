-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.mm_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T05:56:54.140201+00:00
-- url     : https://prove2.me/submissions/eefeaca9-01f2-4f83-addd-d7dd4ad53bcc

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NondegenerateCharts
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieCartFB
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RankMaximalOfNondegenerate
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_mm_zero
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_mm_add

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds
open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
variable {C : Type} [Field C] {V : VF C}
namespace Formalism.L2.FormalSeriesBounds
theorem _root_.solution {ι : Type} (s : Finset ι) (f : ι → C) (hf : ∀ i ∈ s, V.MM (f i)) : V.MM (∑ i ∈ s, f i) := by
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty]
    exact mm_zero
  | insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact mm_add (hf i (Finset.mem_insert_self i s)) (ih fun j hj => hf j (Finset.mem_insert_of_mem hj))
end Formalism.L2.FormalSeriesBounds
