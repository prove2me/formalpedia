-- Prove2me | solution 1 for Egrs75.RepairDV.badIndexSet_nonempty
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:38:36.76463+00:00
-- url     : https://prove2.me/submissions/1541ccd5-c8d8-4315-84cf-44e70c5c539d

module
public import Definitions.Def_LeanPool_Egrs75_LeafInduction
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.List.GetD
public import Mathlib.Data.Nat.Digits.Lemmas
public import Definitions.Def_LeanPool_Egrs75_DigitVector
public import Theorems.Thm_Egrs75_RepairDV_badCountQ_eq

set_option autoImplicit true
@[expose] public section
public section
open Egrs75 Egrs75.RepairDV
open Nat
open Egrs75
open Egrs75.LeafInduction
namespace Egrs75.RepairDV
theorem _root_.solution {q n : ℕ} (_hq : 1 < q) (hbad : 0 < badCountQ q n) :
    (badIndexSet q n).Nonempty := by
  -- A bad digit exists in the list; its position is in `badIndexSet`.
  rw [badCountQ_eq] at hbad
  -- the filtered list is nonempty, so it has a member `d` that is oversized
  have hne : (Nat.digits q n).filter (fun d => bigQ q d) ≠ [] := by
    intro h; rw [h] at hbad; simp at hbad
  obtain ⟨d, hd⟩ := List.exists_mem_of_ne_nil _ hne
  rw [List.mem_filter] at hd
  obtain ⟨hdmem, hdbig⟩ := hd
  obtain ⟨i, hilt, hget⟩ := List.mem_iff_getElem.mp hdmem
  refine ⟨i, ?_⟩
  simp only [badIndexSet, Finset.mem_filter, Finset.mem_range]
  simp_all
end Egrs75.RepairDV
