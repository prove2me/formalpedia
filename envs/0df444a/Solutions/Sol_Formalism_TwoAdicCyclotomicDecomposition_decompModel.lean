-- Prove2me | solution 1 for Formalism.TwoAdicCyclotomicDecomposition.decompModel
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T12:20:31.160847+00:00
-- url     : https://prove2.me/submissions/942c90b7-38d7-4a66-b804-d2de2eee0fcd

import Mathlib
import Definitions.Def_Formalism_TameInertiaTowers_StatementGroup
import Definitions.Def_Formalism_TameInertiaTowers_CentralOrderTwo_MemDecompositionSubgroupIff
import Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_ModelEmbedding_neg_one_ne_one_int
import Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_ModelEmbedding_card_units_int
import Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_ModelEmbedding_mem_zpowers_JJ
import Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_ModelEmbedding_mem_decomposition_subgroup_iff

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
namespace Formalism.TwoAdicCyclotomicDecomposition
theorem _root_.solution : DecompModel := by
  intro n
  have hJ : JJ n ∉ D2 n := by
    rw [mem_decomposition_subgroup_iff, JJ]; exact neg_one_ne_one_int
  refine ⟨hJ, ?_, ?_⟩
  · have hs : Function.Surjective
        ((MonoidHom.snd ℤˣ ℤˣ).comp (MonoidHom.snd (ZMod (2 ^ n))ˣ (ℤˣ × ℤˣ))) :=
      fun e => ⟨(1, 1, e), rfl⟩
    rw [D2, Subgroup.index_ker, MonoidHom.range_eq_top.2 hs, Subgroup.card_top, card_units_int]
  · constructor
    · intro x y hxy
      have hxy' : (QuotientGroup.mk (x : GalL n) : GalL n ⧸ zpowers (JJ n)) =
          QuotientGroup.mk (y : GalL n) := hxy
      have h := QuotientGroup.eq.1 hxy'
      rcases mem_zpowers_JJ h with h1 | h1
      · exact Subtype.ext (inv_mul_eq_one.1 h1)
      · exfalso
        apply hJ
        rw [← h1]
        exact (D2 n).mul_mem ((D2 n).inv_mem x.2) y.2
    · intro q
      obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
      by_cases hg : g ∈ D2 n
      · exact ⟨⟨g, hg⟩, rfl⟩
      · refine ⟨⟨g * JJ n, ?_⟩, ?_⟩
        · rw [mem_decomposition_subgroup_iff] at hg ⊢
          have h2 : g.2.2 = -1 := (Int.units_eq_one_or _).resolve_left hg
          simp [JJ, h2]
        · show (QuotientGroup.mk (g * JJ n) : GalL n ⧸ zpowers (JJ n)) = QuotientGroup.mk g
          refine QuotientGroup.eq.2 ?_
          rw [mul_inv_rev, inv_mul_cancel_right]
          exact inv_mem (mem_zpowers _)
end Formalism.TwoAdicCyclotomicDecomposition
