-- Prove2me | solution 1 for Formalism.TwoAdicCyclotomicDecomposition.gensModel
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T12:02:46.434836+00:00
-- url     : https://prove2.me/submissions/931673ee-1906-45b4-899a-1abcd06a27eb

import Mathlib
import Definitions.Def_Formalism_TameInertiaTowers_StatementGroup
import Definitions.Def_Formalism_TameInertiaTowers_CentralOrderTwo_MemDecompositionSubgroupIff
import Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_ModelEmbedding_neg_one_ne_one_int
import Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_ModelEmbedding_closure_units
import Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_ModelEmbedding_orderOf_eq_two_of_mul_self_eq_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Subgroup
open Formalism Formalism.TwoAdicCyclotomicDecomposition
open ModelEmbedding
open ModelEmbedding
namespace Formalism.TwoAdicCyclotomicDecomposition
theorem _root_.solution : GensModel := by
  intro n hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
  have hI2 : I2 (k + 2) = Subgroup.closure {((-1, 1, 1) : GalL (k + 2)), ((u5 (k + 2), 1, 1) : GalL (k + 2))} := by
    have h1 : I2 (k + 2) =
        (⊤ : Subgroup (ZMod (2 ^ (k + 2)))ˣ).map (MonoidHom.inl (ZMod (2 ^ (k + 2)))ˣ (ℤˣ × ℤˣ)) := by
      ext g
      rw [I2, MonoidHom.mem_ker, Subgroup.mem_map]
      constructor
      · intro h; exact ⟨g.1, Subgroup.mem_top _, Prod.ext rfl h.symm⟩
      · rintro ⟨u, _, rfl⟩; rfl
    rw [h1, ← closure_units k, MonoidHom.map_closure, Set.image_pair]
    rfl
  have hsup : I2 (k + 2) ⊔ Iq (k + 2) ⊔ Id (k + 2) = ⊤ := by
    refine eq_top_iff.2 fun g _ => ?_
    have hg : g = (g.1, 1, 1) * (1, g.2.1, 1) * (1, 1, g.2.2) :=
      Prod.ext (by simp) (Prod.ext (by simp) (by simp))
    rw [hg]
    refine Subgroup.mul_mem_sup (Subgroup.mul_mem_sup ?_ ?_) ?_
    · rw [I2, MonoidHom.mem_ker]; rfl
    · rcases Int.units_eq_one_or g.2.1 with h | h <;> rw [h]
      · exact Subgroup.one_mem _
      · exact Subgroup.mem_zpowers _
    · rcases Int.units_eq_one_or g.2.2 with h | h <;> rw [h]
      · exact Subgroup.one_mem _
      · exact Subgroup.mem_zpowers _
  have hq2 : orderOf ((1, -1, 1) : GalL (k + 2)) = 2 :=
    orderOf_eq_two_of_mul_self_eq_one _ (by simp)
      (fun h => neg_one_ne_one_int (congrArg (fun g : GalL (k + 2) => g.2.1) h))
  have hd2 : orderOf ((1, 1, -1) : GalL (k + 2)) = 2 :=
    orderOf_eq_two_of_mul_self_eq_one _ (by simp)
      (fun h => neg_one_ne_one_int (congrArg (fun g : GalL (k + 2) => g.2.2) h))
  refine ⟨hsup, hI2, by rw [Iq, Nat.card_zpowers, hq2], by rw [Id, Nat.card_zpowers, hd2], ?_⟩
  rw [eq_top_iff, ← hsup]
  refine sup_le (sup_le ?_ ?_) ?_
  · rw [hI2]
    apply Subgroup.closure_mono
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
    tauto
  · rw [Iq]; exact Subgroup.zpowers_le.2 (Subgroup.subset_closure (by simp))
  · rw [Id]; exact Subgroup.zpowers_le.2 (Subgroup.subset_closure (by simp))
end Formalism.TwoAdicCyclotomicDecomposition
