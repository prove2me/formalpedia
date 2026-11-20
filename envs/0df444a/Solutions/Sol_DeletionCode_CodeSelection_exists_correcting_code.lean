-- Prove2me | solution 1 for DeletionCode.CodeSelection.exists_correcting_code
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:46:55.406771+00:00
-- url     : https://prove2.me/submissions/1912f1b4-cb97-487a-9af3-74730b7587ee

import Definitions.Def_DeletionCode_BipartiteSelection
import Definitions.Def_DeletionCode_ConflictGraphWitness
import Definitions.Def_DeletionCode_CodeSelection
import Theorems.Thm_DeletionCode_CodeSelection_wordLabelFin_eq_iff
import Theorems.Thm_DeletionCode_BipartiteSelection_exists_independent_good
import Theorems.Thm_DeletionCode_BipartiteSelection_exists_large_label_fiber
import Theorems.Thm_DeletionCode_ConnectedBlocks_RuleAdjacent_symm
import Theorems.Thm_DeletionCode_EditAlignment_Script_trans


set_option autoImplicit true
open DeletionCode DeletionCode.CodeSelection
open HeaderRecovery ConflictGraphWitness BipartiteSelection
variable {n k : ℕ}
namespace DeletionCode.CodeSelection
theorem _root_.solution (t Q : ℕ) (hQ : 2 ≤ Q)
    (H : Spectrum k →+ UnitAddCircle) :
    ∃ C : Finset (Bits n),
      (goodVertices (graph (n := n) t Q H)).card ≤ 2 * Q * C.card ∧ Corrects t C := by
  classical
  let V := Vertex (n := n) t Q H
  let G : SimpleGraph V := graph t Q H
  obtain ⟨I, _hgood, hind, hhalf⟩ := exists_independent_good G
  let label : V → Fin Q := fun v => wordLabelFin Q hQ H v.val
  obtain ⟨a, hlabelcard⟩ := exists_large_label_fiber I label (by omega)
  let J : Finset V := I.filter (fun v => label v = a)
  let C : Finset (Bits n) := J.image Subtype.val
  have hcard : C.card = J.card := Finset.card_image_of_injective J Subtype.val_injective
  refine ⟨C, ?_, ?_⟩
  · calc
      (goodVertices (graph (n := n) t Q H)).card ≤ 2 * I.card := hhalf
      _ ≤ 2 * (Q * J.card) := Nat.mul_le_mul_left 2 hlabelcard
      _ = 2 * Q * C.card := by rw [hcard, Nat.mul_assoc]
  · intro x hx y hy hxy hconf
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hy
    have hv' := Finset.mem_filter.mp hv
    have hw' := Finset.mem_filter.mp hw
    have hne : v ≠ w := fun heq => hxy (congrArg Subtype.val heq)
    have hlabel : wordLabel Q H v.val = wordLabel Q H w.val :=
      (wordLabelFin_eq_iff Q hQ H v.val w.val).mp (hv'.2.trans hw'.2.symm)
    have hnot : ¬ G.Adj v w := hind hv'.1 hw'.1 hne
    exact hnot ⟨hxy, hconf, hlabel⟩
end DeletionCode.CodeSelection
