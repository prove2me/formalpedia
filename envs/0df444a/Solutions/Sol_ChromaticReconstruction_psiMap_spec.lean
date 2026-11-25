-- Prove2me | solution 1 for ChromaticReconstruction.psiMap_spec
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:54:05.574971+00:00
-- url     : https://prove2.me/submissions/57be4903-bbd2-4bf9-8d0a-7f87c5157cde

import Definitions.Def_RequestProject_PathLeaf
import Definitions.Def_RequestProject_Truncation
import Definitions.Def_RequestProject_PathLeafSwap
import Theorems.Thm_ChromaticReconstruction_rf_involutive
import Theorems.Thm_ChromaticReconstruction_image_image_involutive
import Theorems.Thm_ChromaticReconstruction_sB_spec
import Theorems.Thm_ChromaticReconstruction_hasBrk_of_card
import Theorems.Thm_ChromaticReconstruction_mem_image_rf_iff
import Theorems.Thm_ChromaticReconstruction_swap_subset
import Theorems.Thm_ChromaticReconstruction_sB_swap
import Theorems.Thm_ChromaticReconstruction_map_rf_lf
import Theorems.Thm_ChromaticReconstruction_lf_not_mem
import Theorems.Thm_ChromaticReconstruction_pe_of_mem
import Theorems.Thm_ChromaticReconstruction_compSets_eq_of_mutual
import Theorems.Thm_ChromaticReconstruction_compType_map_equiv
import Theorems.Thm_ChromaticReconstruction_lf_mem_edgeSet
import Theorems.Thm_ChromaticReconstruction_pe_mem_edgeSet
import Theorems.Thm_ChromaticReconstruction_pe_ne_lf
import Theorems.Thm_ChromaticReconstruction_reachable_of_mem


set_option autoImplicit true
open Finset
open scoped Classical
noncomputable section
open ChromaticReconstruction
variable {n c : ℕ}
namespace ChromaticReconstruction
theorem _root_.solution {p : ℕ} {F : Finset (Sym2 (Fin (n + 1)))} (hn : 2 * c + 3 ≤ n)
    (hp : p = c ∨ p = c + 1) (hF : F ⊆ (PL n p).edgeFinset) (hcard : F.card ≤ c + 1) :
    psiMap n c p F ⊆ (PL n (2 * c + 1 - p)).edgeFinset ∧
      compType (psiMap n c p F : Set (Sym2 (Fin (n + 1)))) =
        compType (F : Set (Sym2 (Fin (n + 1)))) ∧
      psiMap n c (2 * c + 1 - p) (psiMap n c p F) = F := by
  have hpn : p < n := by omega
  have hp'n : 2 * c + 1 - p < n := by omega
  have hpp' : p ≠ 2 * c + 1 - p := by omega
  have hpp : 2 * c + 1 - (2 * c + 1 - p) = p := by omega
  have hlf' : lf n (2 * c + 1 - p) ∉ F := lf_not_mem hpn hp'n hpp' hF
  unfold psiMap
  by_cases hl : lf n p ∈ F
  · rw [if_neg (not_not.2 hl)]
    by_cases hg : pe n c ∈ F
    · -- the gap edge is used: move the leaf
      rw [if_pos hg]
      set F' := insert (lf n (2 * c + 1 - p)) (F.erase (lf n p)) with hF'
      have hgF' : pe n c ∈ F' := mem_insert_of_mem (mem_erase.2 ⟨pe_ne_lf (by omega) hpn.le, hg⟩)
      have hlF' : lf n (2 * c + 1 - p) ∈ F' := mem_insert_self _ _
      refine ⟨?_, ?_, ?_⟩
      · intro e he
        rw [hF', mem_insert] at he
        rcases he with rfl | he
        · exact SimpleGraph.mem_edgeFinset.2 (lf_mem_edgeSet hp'n)
        · obtain ⟨hne, he⟩ := mem_erase.1 he
          obtain ⟨i, hi, rfl⟩ := pe_of_mem hpn hF he hne
          exact SimpleGraph.mem_edgeFinset.2 (pe_mem_edgeSet hp'n hi)
      · -- mutual reachability
        have hcc : ∀ (G : Finset (Sym2 (Fin (n + 1)))), pe n c ∈ G →
            (SimpleGraph.fromEdgeSet (G : Set (Sym2 (Fin (n + 1))))).Reachable (vx n p)
              (vx n (2 * c + 1 - p)) := by
          intro G hG
          have := reachable_of_mem (A := (G : Set (Sym2 (Fin (n + 1))))) (u := vx n c)
            (v := vx n (c + 1)) hG
          rcases hp with h | h
          · rw [h, show 2 * c + 1 - c = c + 1 by omega]; exact this
          · rw [h, show 2 * c + 1 - (c + 1) = c by omega]; exact this.symm
        unfold compType
        rw [compSets_eq_of_mutual (A := (F' : Set (Sym2 (Fin (n + 1)))))
          (B := (F : Set (Sym2 (Fin (n + 1))))) ?_ ?_]
        · intro u v huv
          by_cases he : s(u, v) = lf n (2 * c + 1 - p)
          · have hr : (SimpleGraph.fromEdgeSet (F : Set (Sym2 (Fin (n + 1))))).Reachable
                (vx n (2 * c + 1 - p)) (vx n n) :=
              (hcc F hg).symm.trans (reachable_of_mem (A := (F : Set (Sym2 (Fin (n + 1)))))
                (u := vx n p) (v := vx n n) hl)
            rw [lf, Sym2.eq_iff] at he
            rcases he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
            · exact hr
            · exact hr.symm
          · have : s(u, v) ∈ F := by
              have huv' : s(u, v) ∈ F' := huv
              rw [hF', mem_insert] at huv'
              rcases huv' with h | h
              · exact absurd h he
              · exact (mem_erase.1 h).2
            exact reachable_of_mem this
        · intro u v huv
          by_cases he : s(u, v) = lf n p
          · have hr : (SimpleGraph.fromEdgeSet (F' : Set (Sym2 (Fin (n + 1))))).Reachable
                (vx n p) (vx n n) :=
              (hcc F' hgF').trans (reachable_of_mem (A := (F' : Set (Sym2 (Fin (n + 1)))))
                (u := vx n (2 * c + 1 - p)) (v := vx n n) hlF')
            rw [lf, Sym2.eq_iff] at he
            rcases he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
            · exact hr
            · exact hr.symm
          · exact reachable_of_mem (A := (F' : Set (Sym2 (Fin (n + 1)))))
              (mem_insert_of_mem (mem_erase.2 ⟨he, huv⟩))
      · rw [if_neg (not_not.2 hlF'), if_pos hgF', hpp, hF', erase_insert, insert_erase hl]
        intro h
        exact hlf' (mem_erase.1 h).2
    · -- the reflection
      rw [if_neg hg]
      have hb := hasBrk_of_card hn (by omega) hl hcard
      obtain ⟨hs1, hs2, -, -⟩ := sB_spec hb
      have hs : c + sB n c F ≤ n := by omega
      refine ⟨swap_subset hn hp hF hb, ?_, ?_⟩
      · rw [coe_image]
        exact compType_map_equiv (rf_involutive hs hs2).toPerm _
      · have hlF' : lf n (2 * c + 1 - p) ∈ F.image (Sym2.map (rf n c (sB n c F))) :=
          mem_image.2 ⟨_, hl, map_rf_lf hn hp hs1 hs2⟩
        have hgF' : pe n c ∉ F.image (Sym2.map (rf n c (sB n c F))) := by
          rw [pe, mem_image_rf_iff hs hs2 (by omega) (by omega)]
          have e1 : rfv c (sB n c F) c = c + 1 := by unfold rfv; split_ifs <;> omega
          have e2 : rfv c (sB n c F) (c + 1) = c := by unfold rfv; split_ifs <;> omega
          rw [e1, e2, Sym2.eq_swap]
          exact hg
        rw [if_neg (not_not.2 hlF'), if_neg hgF', sB_swap hn hF hb,
          image_image_involutive (rf_involutive hs hs2)]
  · rw [if_pos hl]
    refine ⟨?_, rfl, ?_⟩
    · intro e he
      obtain ⟨i, hi, rfl⟩ := pe_of_mem hpn hF he (fun h => hl (h ▸ he))
      exact SimpleGraph.mem_edgeFinset.2 (pe_mem_edgeSet hp'n hi)
    · rw [if_pos hlf']
end ChromaticReconstruction
