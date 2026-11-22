-- Prove2me | solution 1 for DeciSigma1.Arithmetic.DifferenceSystem.le_maxNonnegativeWeight
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:11:09.332342+00:00
-- url     : https://prove2.me/submissions/1042f816-39f0-4aea-a371-832bde7cbad9

module
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Fintype.Prod
public import Definitions.Def_LeanPool_DeciSigma1_Automata_Basic
public import Mathlib.Tactic.Ring.RingNF
public import Mathlib.Tactic.Linarith
public import Definitions.Def_LeanPool_DeciSigma1_Arithmetic_DifferenceConstraints

set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Arithmetic
open DeciSigma1.Arithmetic.DifferenceSystem
variable {ι : Type} (D : DifferenceSystem ι)
variable {D}
namespace DeciSigma1.Arithmetic.DifferenceSystem
theorem _root_.solution [Fintype ι] {i j : ι} {c : ℤ} (h : D.edgeWeight i j = some c) :
    c ≤ D.maxNonnegativeWeight := by
  have : ((D.edgeWeight i j).getD 0).toNat ≤ D.maxNonnegativeWeight :=
    Finset.le_sup (f := fun ij : ι × ι => ((D.edgeWeight ij.1 ij.2).getD 0).toNat)
      (Finset.mem_univ (i, j))
  rw [h, Option.getD_some] at this
  omega
end DeciSigma1.Arithmetic.DifferenceSystem
