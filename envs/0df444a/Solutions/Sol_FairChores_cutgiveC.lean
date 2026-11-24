-- Prove2me | solution 1 for FairChores.cutgiveC
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:28:01.669076+00:00
-- url     : https://prove2.me/submissions/8175e0e4-2640-4a9b-a82b-a58644705024

import Mathlib
import Definitions.Def_RequestProject_ChoresMMSPartition
import Definitions.Def_RequestProject_ChoresPreAlloc
import Definitions.Def_RequestProject_ChoresTwoAgents
import Theorems.Thm_FairChores_biU_twoC
import Theorems.Thm_FairChores_realize2C
import Theorems.Thm_FairChores_cbarSum_sdiff


set_option autoImplicit true
open scoped BigOperators
open FairChores
variable {T : Type*} [Fintype T] [DecidableEq T]
namespace FairChores
theorem _root_.solution (c : Fin 2 → T → ℝ) (p : T → ℝ) (hp : ∀ t, 0 ≤ p t)
    (Ac : Fin 2 → Finset T) (sc : Finset T) (qc : Fin 2 → ℝ)
    (hc : ConfigC (c 0) p (MMS 2 (c 0) p) Ac sc qc)
    (sg : Finset T) (hsg : sg.card ≤ 1)
    (hbound : cbarSum (c 1) p (Finset.univ \ sg) + ∑ t ∈ sg, p t ≤ 2 * MMS 2 (c 1) p)
    (hcut : ∑ t ∈ sc, p t ≤ ∑ t ∈ sg, p t) :
    ∃ o : Outcome T 2, o.Valid p ∧
      cost (c 0) o 0 ≤ MMS 2 (c 0) p ∧ cost (c 1) o 1 ≤ MMS 2 (c 1) p := by
  classical
  obtain ⟨hdisjA, hdisjs, hcover, hq0, hsat, hle⟩ := hc
  set M0 := MMS 2 (c 0) p
  set M1 := MMS 2 (c 1) p
  have hqsum : qc 0 + qc 1 = ∑ t ∈ sc, p t := by rw [← Fin.sum_univ_two qc]; exact hsat
  have hcoverC : sc ∪ (Ac 0 ∪ Ac 1) = Finset.univ := by rw [← biU_twoC Ac]; exact hcover
  by_cases hCC : ∃ t : Fin 2, cbarSum (c 1) p (Ac t) + qc t ≤ M1
  · -- Cut & Choose: the Giver takes an acceptable part, the Cutter the other one
    obtain ⟨t, ht⟩ := hCC
    fin_cases t
    · obtain ⟨o, hov, h0, h1⟩ := realize2C c p hp (Ac 1) (Ac 0) sc (qc 1) (qc 0)
        (hdisjA 1 0 (by decide)) (hdisjs 1) (hdisjs 0)
        (by rw [Finset.union_comm (Ac 1) (Ac 0)]; exact hcoverC)
        (hq0 1) (hq0 0) (by rw [add_comm]; exact hqsum)
      exact ⟨o, hov, by rw [h0]; exact hle 1, by rw [h1]; exact ht⟩
    · obtain ⟨o, hov, h0, h1⟩ := realize2C c p hp (Ac 0) (Ac 1) sc (qc 0) (qc 1)
        (hdisjA 0 1 (by decide)) (hdisjs 0) (hdisjs 1) hcoverC (hq0 0) (hq0 1) hqsum
      exact ⟨o, hov, by rw [h0]; exact hle 0, by rw [h1]; exact ht⟩
  · -- Cut & Give: no part is acceptable to the Giver
    push_neg at hCC
    have htex : ∃ t : Fin 2, Disjoint (Ac t) sg := by
      by_cases hd0 : Disjoint (Ac 0) sg
      · exact ⟨0, hd0⟩
      · refine ⟨1, ?_⟩
        rw [Finset.not_disjoint_iff] at hd0
        obtain ⟨x, hxA, hxs⟩ := hd0
        rw [Finset.disjoint_left]
        intro y hyA hys
        have hxy : x = y := Finset.card_le_one.mp hsg x hxs y hys
        subst hxy
        exact Finset.disjoint_left.mp (hdisjA 1 0 (by decide)) hyA hxA
    obtain ⟨t, htd⟩ := htex
    have hAtsub : Ac t ⊆ Finset.univ \ sg := Finset.subset_sdiff.mpr ⟨Finset.subset_univ _, htd⟩
    have hqct_le : qc t ≤ ∑ t ∈ sg, p t := by
      have hle' : qc t ≤ qc 0 + qc 1 := by
        rcases (show t = 0 ∨ t = 1 by omega) with h | h <;> subst h <;> linarith [hq0 0, hq0 1]
      linarith [hqsum, hcut]
    obtain ⟨o, hov, h0, h1⟩ := realize2C c p hp (Ac t) ((Finset.univ \ Ac t) \ sg) sg
      (qc t) ((∑ t ∈ sg, p t) - qc t)
      (Finset.disjoint_left.mpr fun y hy hy2 =>
        (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hy2).1).2 hy)
      htd.symm
      (Finset.disjoint_left.mpr fun y hy hy2 => (Finset.mem_sdiff.mp hy2).2 hy)
      (by
        apply Finset.eq_univ_of_forall
        intro x
        by_cases hxg : x ∈ sg
        · exact Finset.mem_union_left _ hxg
        · by_cases hxA : x ∈ Ac t
          · exact Finset.mem_union_right _ (Finset.mem_union_left _ hxA)
          · refine Finset.mem_union_right _ (Finset.mem_union_right _ ?_)
            exact Finset.mem_sdiff.mpr ⟨Finset.mem_sdiff.mpr ⟨Finset.mem_univ x, hxA⟩, hxg⟩)
      (hq0 t) (by linarith [hqct_le]) (by ring)
    refine ⟨o, hov, by rw [h0]; exact hle t, ?_⟩
    rw [h1]
    have hB1eq : (Finset.univ \ Ac t) \ sg = (Finset.univ \ sg) \ Ac t := sdiff_sdiff_comm
    have hcbsd : cbarSum (c 1) p ((Finset.univ \ Ac t) \ sg)
        = cbarSum (c 1) p (Finset.univ \ sg) - cbarSum (c 1) p (Ac t) := by
      rw [hB1eq]
      have := cbarSum_sdiff (c 1) p hAtsub
      linarith
    rw [hcbsd]
    linarith [hbound, hCC t]
end FairChores
