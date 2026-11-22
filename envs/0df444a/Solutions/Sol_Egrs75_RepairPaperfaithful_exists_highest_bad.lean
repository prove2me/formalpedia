-- Prove2me | solution 1 for Egrs75.RepairPaperfaithful.exists_highest_bad
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:31:40.955686+00:00
-- url     : https://prove2.me/submissions/4150cf3a-f808-4b9f-9349-332874180d22

module
public import Definitions.Def_LeanPool_Egrs75_LeafInduction
public import Mathlib.Data.List.GetD
public import Mathlib.Data.Nat.Digits.Lemmas
public import Definitions.Def_LeanPool_Egrs75_DigitAtToolkit

set_option autoImplicit true
@[expose] public section
public section
open Egrs75 Egrs75.RepairPaperfaithful
open Nat
open Egrs75
open Egrs75.LeafInduction
namespace Egrs75.RepairPaperfaithful
theorem _root_.solution {q n : ℕ} (hq : 2 ≤ q) (hbad : 0 < badCountQ q n) :
    ∃ j, BadAt q j n ∧ ∀ i, BadAt q i n → i ≤ j := by
  -- From a positive filter-length, the filtered list is nonempty, giving a bad member,
  -- which sits at some index of `digits q n`; bad indices are `< length`, hence bounded.
  have hne : badDigitsQ q n ≠ [] := by
    intro h; rw [badCountQ, h] at hbad; simp at hbad
  -- there is a bad digit value `d` in the list
  obtain ⟨d, hd⟩ := List.exists_mem_of_ne_nil _ hne
  -- The set of bad indices is nonempty and bounded by the digit-list length.
  have hbddSet : ∃ i, BadAt q i n := by
    -- `d ∈ badDigitsQ` means `d ∈ digits q n` and `(q-1)/2 < d`; `d` sits at some index.
    rw [badDigitsQ, List.mem_filter] at hd
    obtain ⟨hmem, hdec⟩ := hd
    obtain ⟨i, hi, hget⟩ := List.mem_iff_getElem.mp hmem
    refine ⟨i, ?_⟩
    unfold BadAt digitAt
    rw [← getD_digits n i hq, List.getD_eq_getElem _ 0 hi, hget]
    simpa using hdec
  -- Bound: any bad index `i` is `< length` (digits beyond length are 0, not bad).
  have hbound : ∀ i, BadAt q i n → i < (Nat.digits q n).length := by
    intro i hbi
    by_contra hcon
    have hge : (Nat.digits q n).length ≤ i := Nat.le_of_not_lt hcon
    unfold BadAt digitAt at hbi
    rw [← getD_digits n i hq, List.getD_eq_default _ 0 hge] at hbi
    omega
  -- Maximum of a nonempty set of naturals bounded above exists.
  classical
  obtain ⟨i0, hi0⟩ := hbddSet
  -- Use Nat.findGreatest with bound = length and a classical decidability instance.
  set P : ℕ → Prop := fun j => BadAt q j n with hP
  set L := (Nat.digits q n).length with hL
  have hi0L : i0 ≤ L := le_of_lt (hbound i0 hi0)
  refine ⟨Nat.findGreatest P L, ?_, ?_⟩
  · exact Nat.findGreatest_spec (P := P) hi0L hi0
  · intro i hbi
    exact Nat.le_findGreatest (le_of_lt (hbound i hbi)) hbi
end Egrs75.RepairPaperfaithful
