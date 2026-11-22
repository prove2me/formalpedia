-- Prove2me | solution 1 for DeciSigma1.Arithmetic.DifferenceSystem.Sat.add_const
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:11:03.335739+00:00
-- url     : https://prove2.me/submissions/b3eebc0d-1675-4377-894e-6902bfa22c59

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
namespace Sat
theorem _root_.solution {x : ι → ℤ} (h : D.Sat x) (c : ℤ) : D.Sat (fun i => x i + c) := by
  intro i j d hd
  have := h i j d hd
  linarith
end Sat
end DeciSigma1.Arithmetic.DifferenceSystem
