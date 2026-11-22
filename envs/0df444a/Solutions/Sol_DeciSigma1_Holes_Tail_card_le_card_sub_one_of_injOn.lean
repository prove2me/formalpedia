-- Prove2me | solution 1 for DeciSigma1.Holes.Tail.card_le_card_sub_one_of_injOn
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:54:17.310894+00:00
-- url     : https://prove2.me/submissions/cbbece4c-f284-4829-8d94-4008d04555ca

module
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Periodic_Basic
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Tail_ClosedFactors
public import Mathlib.Order.Nat
public import Mathlib.Data.Nat.ModEq
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Data.Fintype.Pigeonhole
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Tactic.Ring.RingNF
public import Mathlib.Algebra.GroupWithZero.Nat
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Tail_Levels
public import Theorems.Thm_DeciSigma1_Holes_Periodic_FollowerEdge_symm
public import Theorems.Thm_DeciSigma1_Words_IsConjugate_symm


set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Tail
open DeciSigma1.Holes.Periodic DeciSigma1.Readers DeciSigma1.Words
variable {α S : Type} {k : ℕ}
namespace DeciSigma1.Holes.Tail
theorem _root_.solution {κ S : Type*} [Fintype S] (A : Finset κ)
    (key : κ → ℕ) (hkey : Set.InjOn key A) (f : κ → S) (d : S)
    (hinj : ∀ x ∈ A, ∀ y ∈ A, key x < key y → f x ≠ f y) (hd : ∀ x ∈ A, f x ≠ d) :
    A.card ≤ Fintype.card S - 1 := by
  classical
  have h := Finset.card_le_card_of_injOn f (t := Finset.univ.erase d)
    (fun x hx => Finset.mem_coe.mpr (Finset.mem_erase.mpr ⟨hd x hx, Finset.mem_univ _⟩))
    (fun x hx y hy he => by
      by_contra hne
      rcases Nat.lt_or_gt_of_ne fun h => hne (hkey hx hy h) with h | h
      · exact hinj x hx y hy h he
      · exact hinj y hy x hx h he.symm)
  rwa [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ] at h
end DeciSigma1.Holes.Tail
