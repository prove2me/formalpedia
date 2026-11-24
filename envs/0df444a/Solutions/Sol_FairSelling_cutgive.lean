-- Prove2me | solution 1 for FairSelling.cutgive
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:30:39.863518+00:00
-- url     : https://prove2.me/submissions/ed130179-f7ad-4541-8ffd-1bb24c07a7bf

import Mathlib
import Definitions.Def_RequestProject_SmallN
import Definitions.Def_RequestProject_TwoAgents
import Theorems.Thm_FairSelling_vbarSum_sdiff
import Theorems.Thm_FairSelling_realize2

set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G]
namespace FairSelling
theorem _root_.solution (v : Fin 2 → G → ℝ) (p : G → ℝ) (hp : ∀ g, 0 ≤ p g)
    (Ac : Fin 2 → Finset G) (sc : Finset G) (qc : Fin 2 → ℝ)
    (hc : Config (v 0) p (MMS 2 (v 0) p) Ac sc qc)
    (sg : Finset G) (hsg : sg.card ≤ 1)
    (hbound : 2 * MMS 2 (v 1) p ≤ vbarSum (v 1) p (Finset.univ \ sg) + ∑ g ∈ sg, p g)
    (hcut : ∑ g ∈ sc, p g ≤ ∑ g ∈ sg, p g) :
    ∃ o : Outcome G 2, o.Valid p ∧
      MMS 2 (v 0) p ≤ util (v 0) o 0 ∧ MMS 2 (v 1) p ≤ util (v 1) o 1 := by
  obtain ⟨hdisjA, hdisjs, hcover, hq0, hsat, hge⟩ := hc
  set M0 := MMS 2 (v 0) p
  set M1 := MMS 2 (v 1) p
  have hqsum : qc 0 + qc 1 = ∑ g ∈ sc, p g := by rw [← Fin.sum_univ_two qc]; exact hsat
  by_cases hCC : ∃ t : Fin 2, M1 ≤ vbarSum (v 1) p (Ac t) + qc t
  · obtain ⟨t, ht⟩ := hCC
    fin_cases t
    · obtain ⟨o, hov, h0, h1⟩ := realize2 v p hp (Ac 1) (Ac 0) sc (qc 1) (qc 0)
        (hdisjA 1 0 (by decide)) (hdisjs 1) (hdisjs 0) (hq0 1) (hq0 0)
        (by rw [add_comm]; exact le_of_eq hqsum)
      exact ⟨o, hov, by rw [h0]; exact hge 1, by rw [h1]; exact ht⟩
    · obtain ⟨o, hov, h0, h1⟩ := realize2 v p hp (Ac 0) (Ac 1) sc (qc 0) (qc 1)
        (hdisjA 0 1 (by decide)) (hdisjs 0) (hdisjs 1) (hq0 0) (hq0 1) (le_of_eq hqsum)
      exact ⟨o, hov, by rw [h0]; exact hge 0, by rw [h1]; exact ht⟩
  · push_neg at hCC
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
    have hqct_le : qc t ≤ ∑ g ∈ sg, p g := by
      have hle : qc t ≤ qc 0 + qc 1 := by
        rcases (show t = 0 ∨ t = 1 by omega) with h | h <;> subst h <;> linarith [hq0 0, hq0 1]
      linarith [hqsum, hcut]
    obtain ⟨o, hov, h0, h1⟩ := realize2 v p hp (Ac t) ((Finset.univ \ Ac t) \ sg) sg
      (qc t) ((∑ g ∈ sg, p g) - qc t)
      (Finset.disjoint_left.mpr fun y hy hy2 =>
        (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hy2).1).2 hy)
      htd.symm
      (Finset.disjoint_left.mpr fun y hy hy2 => (Finset.mem_sdiff.mp hy2).2 hy)
      (hq0 t) (by linarith [hqct_le]) (by linarith)
    refine ⟨o, hov, by rw [h0]; exact hge t, ?_⟩
    rw [h1]
    have hB1eq : (Finset.univ \ Ac t) \ sg = (Finset.univ \ sg) \ Ac t := sdiff_sdiff_comm
    have hvsdiff : vbarSum (v 1) p ((Finset.univ \ Ac t) \ sg)
        = vbarSum (v 1) p (Finset.univ \ sg) - vbarSum (v 1) p (Ac t) := by
      rw [hB1eq]; exact vbarSum_sdiff (v 1) p hAtsub
    rw [hvsdiff]
    linarith [hbound, hCC t]
end FairSelling
