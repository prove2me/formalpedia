-- Prove2me | solution 1 for Erdos1219.Ctx.exists_homog
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:51:40.837804+00:00
-- url     : https://prove2.me/submissions/783bdf46-8a3c-4a36-885a-88d1fa4b6bd7

import Definitions.Def_Erdos1219_Defs
import Definitions.Def_Erdos1219_CardinalLemmas
import Definitions.Def_Erdos1219_Ramsey
import Definitions.Def_Erdos1219_UnbalancedErdosRado
import Definitions.Def_Erdos1219_Canonization
import Theorems.Thm_Erdos1219_Ctx_Bu_subset_A
import Theorems.Thm_Erdos1219_Ctx_cross
import Theorems.Thm_Erdos1219_Ctx_part_subset_Bu
import Theorems.Thm_Erdos1219_Ctx_part_homog
import Theorems.Thm_Erdos1219_Ctx_mk_part
import Theorems.Thm_Erdos1219_Homog_mono
import Theorems.Thm_Erdos1219_mk_iUnion_nat_eq_sum
import Theorems.Thm_Erdos1219_ramsey_nat
import Theorems.Thm_Erdos1219_sum_aleph_eq_aleph_omega


set_option autoImplicit false
open Cardinal Ordinal Function
open Erdos1219
universe u
open Erdos1219.Ctx
variable {V : Type u} (S : Ctx V)
namespace Erdos1219.Ctx
theorem _root_.solution : ∃ (c : Bool) (H : Set V), #H = ℵ_ ω ∧ Homog S.f c H := by
  obtain ⟨m, δ, hm, hδ⟩ := ramsey_nat S.g
  refine ⟨δ, ⋃ p, S.part δ (m p), ?_, ?_⟩
  · have hdisj' : Pairwise (Disjoint on fun p => S.part δ (m p)) := by
      intro p q hpq
      exact Set.disjoint_of_subset (S.part_subset_Bu δ (m p)) (S.part_subset_Bu δ (m q))
        ((S.hdisj _ _ (hm.injective.ne hpq)).mono (S.Bu_subset_A _) (S.Bu_subset_A _))
    rw [mk_iUnion_nat_eq_sum _ hdisj']
    simp only [S.mk_part]
    exact sum_aleph_eq_aleph_omega (fun p => S.n (m p))
      (fun N => (hm.id_le N).trans (S.hn.id_le _))
  · intro x hx y hy hxy
    obtain ⟨p, hxp⟩ := Set.mem_iUnion.1 hx
    obtain ⟨q, hyq⟩ := Set.mem_iUnion.1 hy
    rcases lt_trichotomy p q with h | rfl | h
    · rw [S.cross (hm h) (S.part_subset_Bu _ _ hxp) (S.part_subset_Bu _ _ hyq)]
      exact hδ p q h
    · exact S.part_homog δ (m p) x hxp y hyq hxy
    · rw [S.hf, S.cross (hm h) (S.part_subset_Bu _ _ hyq) (S.part_subset_Bu _ _ hxp)]
      exact hδ q p h
end Erdos1219.Ctx
