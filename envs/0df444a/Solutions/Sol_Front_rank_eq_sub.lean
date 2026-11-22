-- Prove2me | solution 1 for Front.rank_eq_sub
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:43:38.17191+00:00
-- url     : https://prove2.me/submissions/6d9a493d-496e-4356-8605-26a8cad7c8ed

module
public import Definitions.Def_LeanPool_NashWilliams_Combinatorics_Front_Defs
public import Mathlib.SetTheory.Ordinal.Rank
public import Mathlib.Order.Lattice.Nat
public import Definitions.Def_LeanPool_NashWilliams_Combinatorics_Front_Rank
public import Theorems.Thm_Front_IsInit_eq_of_length
public import Theorems.Thm_Front_isInit_nil
attribute [local simp] Front.isInit_nil



set_option autoImplicit true
@[expose] public section
public section
open Set List Ordinal
universe u
noncomputable section
open Front
variable {F : Set (List ℕ)} {M : ℕ → ℕ}
namespace Front
theorem _root_.solution (hF : IsFront F M) {s0 : List ℕ} (L : ℕ)
    (hbound : ∀ s, s0 <+: s → s ∈ tree F → s.length ≤ L)
    (hext : ∀ s, s0 <+: s → s ∈ tree F → s.length < L → ∃ x, treeExt F (s ++ [x]) s)
    (s : List ℕ) (hs0 : s0 <+: s) (hs : s ∈ tree F) :
    letI : IsWellFounded (List ℕ) (treeExt F) := ⟨hF.wellFounded_treeExt⟩
    IsWellFounded.rank (treeExt F) s = ((L - s.length : ℕ) : Ordinal) := by
  letI : IsWellFounded (List ℕ) (treeExt F) := ⟨hF.wellFounded_treeExt⟩
  suffices H : ∀ d s, s0 <+: s → s ∈ tree F → L - s.length = d →
      IsWellFounded.rank (treeExt F) s = (d : Ordinal) by
    exact H _ s hs0 hs rfl
  intro d
  induction d using Nat.strong_induction_on with
  | _ d IH =>
    intro s hs0 hs hd
    rw [IsWellFounded.rank_eq]
    apply le_antisymm
    · apply Ordinal.iSup_le
      rintro ⟨y, hytree, -, hsy, hsney⟩
      have hslt : s.length < y.length :=
        lt_of_le_of_ne hsy.length_le fun h => hsney (hsy.eq_of_length h)
      have hs0y : s0 <+: y := hs0.trans hsy
      have hyL : y.length ≤ L := hbound y hs0y hytree
      have hsL : s.length ≤ L := hbound s hs0 hs
      have := IH _ (show L - y.length < d by omega) y hs0y hytree rfl
      rw [this, Order.succ_eq_add_one, ← Nat.cast_add_one, Nat.cast_le]
      omega
    · rcases Nat.eq_zero_or_pos d with hd0 | hdpos
      · simp [hd0]
      · have hsL : s.length ≤ L := hbound s hs0 hs
        obtain ⟨x, hx⟩ := hext s hs0 hs (by omega)
        have hs0x : s0 <+: s ++ [x] := hs0.trans (List.prefix_append s [x])
        have hrank := IH (d - 1) (by omega) (s ++ [x]) hs0x hx.1 (by simp; omega)
        calc ((d : ℕ) : Ordinal) = Order.succ (((d - 1 : ℕ) : Ordinal)) := by
              rw [Order.succ_eq_add_one, ← Nat.cast_add_one]
              congr 1
              omega
          _ = Order.succ (IsWellFounded.rank (treeExt F) (s ++ [x])) := by rw [hrank]
          _ ≤ _ := Ordinal.le_iSup
              (fun b : {b // treeExt F b s} =>
                Order.succ (IsWellFounded.rank (treeExt F) (b : List ℕ)))
              ⟨s ++ [x], hx⟩
end Front
