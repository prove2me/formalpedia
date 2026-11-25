-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.ValuationNonnegativity.frob_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:51:15.814125+00:00
-- url     : https://prove2.me/submissions/4de5a7d9-5209-4325-a066-dd323e68ec80

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieFB
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_IndependenceBoundRaw
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_ValuationNonnegativity_mm_zero
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_ValuationNonnegativity_mm_add
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_ValuationNonnegativity_frob2
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_sum
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_sum


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
theorem _root_.solution {ι : Type*} (s : Finset ι) (f : ι → C) (hf : ∀ i ∈ s, V.Ge 0 (f i)) :
    V.MM ((∑ i ∈ s, f i) ^ V.l - ∑ i ∈ s, f i ^ V.l) := by
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty, zero_pow V.l_prime.ne_zero, sub_zero]; exact mm_zero
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    have hs : V.Ge 0 (∑ j ∈ s, f j) := VF.Ge.sum fun j hj => hf j (Finset.mem_insert_of_mem hj)
    have h1 := frob2 (hf i (Finset.mem_insert_self i s)) hs
    have h2 := ih fun j hj => hf j (Finset.mem_insert_of_mem hj)
    have e : (f i + ∑ j ∈ s, f j) ^ V.l - (f i ^ V.l + ∑ j ∈ s, f j ^ V.l) =
        ((f i + ∑ j ∈ s, f j) ^ V.l - f i ^ V.l - (∑ j ∈ s, f j) ^ V.l) +
          ((∑ j ∈ s, f j) ^ V.l - ∑ j ∈ s, f j ^ V.l) := by ring
    rw [e]; exact mm_add h1 h2
end Formalism.L2.FormalSeriesBounds.ValuationNonnegativity
