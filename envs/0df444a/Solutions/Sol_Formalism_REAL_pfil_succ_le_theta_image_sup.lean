-- Prove2me | solution 1 for Formalism.REAL.pfil_succ_le_theta_image_sup
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T11:35:08.961826+00:00
-- url     : https://prove2.me/submissions/4695a662-3450-41bc-b273-bfcc2f420033

import Definitions.Def_Formalism_RealPlaceAnalysis_StatementU
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_NoncompactGeneratorRaisesPfil
import Theorems.Thm_Formalism_REAL_word_action_mem_pfil
import Theorems.Thm_Formalism_REAL_symmetrization_apply
import Theorems.Thm_Formalism_REAL_mem_noncompact_arr_iff

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
theorem _root_.solution (j : ℕ) : pfil ε E u (j + 1) ≤
    (arrV0 ε E u (j + 1)).map (thetaA E (j + 1)) ⊔ pfil ε E u j := by
  apply Submodule.span_le.mpr
  rintro z ⟨w, hw, hnc, y, hy, rfl⟩
  rw [SetLike.mem_coe]
  by_cases hlen : w.length ≤ j
  · exact Submodule.mem_sup_right (word_action_mem_pfil ε E u j w hlen hnc y hy)
  · have hl : w.length = j + 1 := by omega
    apply Submodule.mem_sup_left
    let α0 : Fin (j + 1) → Fin n × Fin n := fun i =>
      w.reverse.get ⟨i, by rw [List.length_reverse, hl]; exact i.isLt⟩
    have hα0 : (List.ofFn α0).reverse = w := by
      rw [List.reverse_eq_iff]
      first
      | (apply List.ext_get (by simp [hl]); intro k h1 h2; rw [List.get_ofFn]; rfl)
      | (apply List.ext_getElem (by simp [hl]); intro k h1 h2; rw [List.getElem_ofFn]; rfl)
    have hnc0 : ∀ i, ε (α0 i).1 ≠ ε (α0 i).2 := by
      intro i
      have hm : α0 i ∈ w.reverse := by
        first
        | exact List.get_mem _ _
        | exact List.get_mem _ _ _
        | simp [α0, List.getElem_mem]
      exact hnc (α0 i) (List.mem_reverse.mp hm)
    let F : Arr V n (j + 1) :=
      (WithLp.linearEquiv 2 ℂ ((Fin (j + 1) → Fin n × Fin n) → V)).symm
        (fun β => if β = α0 then y else 0)
    have hF : ∀ β, F β = if β = α0 then y else 0 := fun β => rfl
    rw [Submodule.mem_map]
    refine ⟨F, ?_, ?_⟩
    · rw [mem_noncompact_arr_iff]
      intro β
      rw [hF]
      by_cases hb : β = α0
      · rw [if_pos hb, hb, if_pos hnc0]
        exact hy
      · rw [if_neg hb]
        exact Submodule.zero_mem _
    · rw [symmetrization_apply (E := E) (F := F), Finset.sum_eq_single α0]
      · rw [hF, if_pos rfl, hα0]
      · intro β _ hb
        rw [hF, if_neg hb, map_zero]
      · intro h
        exact absurd (Finset.mem_univ _) h
end Formalism.REAL
