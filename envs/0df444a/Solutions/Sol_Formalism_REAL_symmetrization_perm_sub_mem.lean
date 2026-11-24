-- Prove2me | solution 1 for Formalism.REAL.symmetrization_perm_sub_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T11:44:10.668883+00:00
-- url     : https://prove2.me/submissions/97f6b5a2-bfeb-44b8-b852-94790b84b4e7

import Definitions.Def_Formalism_RealPlaceAnalysis_StatementU
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_NoncompactGeneratorRaisesPfil
import Theorems.Thm_Formalism_REAL_symmetrization_apply
import Theorems.Thm_Formalism_REAL_mem_noncompact_arr_iff
import Theorems.Thm_Formalism_REAL_perm_arr_apply
import Theorems.Thm_Formalism_REAL_reverse_of_fn_noncompact
import Theorems.Thm_Formalism_REAL_permuted_words_diff_mem_pfil

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped InnerProductSpace
open Finset
noncomputable section
open Formalism Formalism.REAL
variable {V : Type} [AddCommGroup V] [Module ℂ V] {n : ℕ} (ε : Fin n → Bool)
    (E : Fin n → Fin n → Module.End ℂ V) (u : V)
namespace Formalism.REAL
theorem _root_.solution (hE : GlRel E) (j : ℕ) (F : Arr V n (j + 1)) (hF : F ∈ arrV0 ε E u (j + 1))
    (σ : Equiv.Perm (Fin (j + 1))) :
    thetaA E (j + 1) (permArr V n σ F) - thetaA E (j + 1) F ∈ pfil ε E u j := by
  let e : (Fin (j + 1) → Fin n × Fin n) ≃ (Fin (j + 1) → Fin n × Fin n) :=
    ⟨fun β => β ∘ σ.symm, fun α => α ∘ σ, fun α => by funext i; simp, fun β => by funext i; simp⟩
  rw [symmetrization_apply (E := E) (F := permArr V n σ F), symmetrization_apply (E := E) (F := F)]
  simp only [perm_arr_apply]
  rw [← Equiv.sum_comp e, ← Finset.sum_sub_distrib]
  refine sum_mem (fun β _ => ?_)
  have he1 : e β = β ∘ σ.symm := rfl
  have he2 : (fun i => e β (σ i)) = β := by
    funext i
    simp [he1]
  rw [he2, he1]
  have hβ := (mem_noncompact_arr_iff ε E u F).mp hF β
  by_cases h : ∀ i, ε (β i).1 ≠ ε (β i).2
  · rw [if_pos h] at hβ
    have hperm : (List.ofFn (β ∘ σ.symm)).reverse.Perm (List.ofFn β).reverse := by
      have h0 : (List.ofFn (β ∘ σ.symm)).Perm (List.ofFn β) := by
        first
        | exact Equiv.Perm.ofFn_comp_perm σ.symm β
        | exact List.ofFn_comp_perm σ.symm β
      exact (List.reverse_perm _).trans (h0.trans (List.reverse_perm _).symm)
    exact permuted_words_diff_mem_pfil ε E u hE (F β) hβ _ _ hperm
      (reverse_of_fn_noncompact ε (β ∘ σ.symm) (fun i => h (σ.symm i))) j (by simp)
  · rw [if_neg h, Submodule.mem_bot] at hβ
    rw [hβ, map_zero, map_zero, sub_zero]
    exact Submodule.zero_mem _
end Formalism.REAL
