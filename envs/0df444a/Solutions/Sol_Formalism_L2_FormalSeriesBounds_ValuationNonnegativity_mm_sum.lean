-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.ValuationNonnegativity.mm_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:33:25.76592+00:00
-- url     : https://prove2.me/submissions/2fd023ff-0d6b-485d-8c42-c1bbbdf1d10f

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieFB
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_IndependenceBoundRaw
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_ValuationNonnegativity_mm_zero
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_ValuationNonnegativity_mm_add

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds
open Formalism.L2.FormalSeriesBounds.ValuationNonnegativity
variable {C : Type} [Field C] {V : VF C}
namespace Formalism.L2.FormalSeriesBounds.ValuationNonnegativity
theorem _root_.solution {ι : Type*} {s : Finset ι} {f : ι → C} (h : ∀ i ∈ s, V.MM (f i)) : V.MM (∑ i ∈ s, f i) :=
  Finset.sum_induction f (fun x => V.MM x) (fun _ _ => mm_add) mm_zero h
end Formalism.L2.FormalSeriesBounds.ValuationNonnegativity
