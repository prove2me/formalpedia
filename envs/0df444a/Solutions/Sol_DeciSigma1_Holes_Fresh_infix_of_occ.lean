-- Prove2me | solution 1 for DeciSigma1.Holes.Fresh.infix_of_occ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:49:19.82263+00:00
-- url     : https://prove2.me/submissions/1a304d98-d83b-4135-886a-baae2f270c88

module
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Definitions.Def_LeanPool_DeciSigma1_Readers_Basic
public import Mathlib.Order.Nat
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Order.Interval.Finset.Nat
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_Hierarchy
public import Theorems.Thm_DeciSigma1_Automata_mem_wordsUpTo
public import Theorems.Thm_DeciSigma1_runFrom_cons
public import Theorems.Thm_DeciSigma1_runFrom_nil
public import Theorems.Thm_DeciSigma1_runFrom_snoc
attribute [local simp] DeciSigma1.Automata.mem_wordsUpTo
attribute [local simp] DeciSigma1.runFrom_cons
attribute [local simp] DeciSigma1.runFrom_nil
attribute [local simp] DeciSigma1.runFrom_snoc



set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Fresh
open DeciSigma1.Readers
open Finset
variable {α : Type} {k : ℕ}
variable {x u v : List α}
namespace DeciSigma1.Holes.Fresh
theorem _root_.solution {i j : ℕ} (hu : u <+: x.drop i) (hv : v <+: x.drop j) (hij : i ≤ j)
    (hlen : j + v.length ≤ i + u.length) : v <:+: u := by
  obtain ⟨r, hr⟩ := hu
  have hd : x.drop j = u.drop (j - i) ++ r := by
    rw [show j = i + (j - i) by omega, ← List.drop_drop, ← hr,
      List.drop_append_of_le_length (by omega), Nat.add_sub_cancel_left]
  rw [hd] at hv
  have h1 : v <+: u.drop (j - i) :=
    List.prefix_of_prefix_length_le hv (List.prefix_append _ _) (by simp; omega)
  exact List.infix_iff_prefix_suffix.mpr ⟨_, h1, List.drop_suffix _ _⟩
end DeciSigma1.Holes.Fresh
