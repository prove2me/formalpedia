-- Prove2me | solution 1 for EconomicsNextProof.upperMobius_const
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:14:27.56169+00:00
-- url     : https://prove2.me/submissions/b244afb9-2a26-403f-bb30-1f88c9f682cc

module
public import Mathlib.Data.Real.Basic
public import Mathlib.Data.Finset.Interval
public import Mathlib.Data.Nat.Choose.Sum
public import Mathlib.Combinatorics.Enumerative.IncidenceAlgebra
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.Tactic
public import Definitions.Def_EconomicsNextProof_Mobius
public import Theorems.Thm_EconomicsNextProof_alternating_interval

set_option autoImplicit true
@[expose] public section
public section
open EconomicsNextProof
open Finset
variable {X : Type*} [Fintype X] [DecidableEq X]
namespace EconomicsNextProof
theorem _root_.solution (c : ℝ) (A : Finset X) :
    upperMobius (fun _ => c) A = if A = Finset.univ then c else 0 := by
  have hs : Finset.univ.filter (fun B : Finset X => A ⊆ B) =
      Finset.Icc A Finset.univ := by
    ext B
    simp
  rw [upperMobius, hs, ← Finset.sum_mul,
    alternating_interval A Finset.univ (Finset.subset_univ A)]
  split_ifs <;> simp
end EconomicsNextProof
