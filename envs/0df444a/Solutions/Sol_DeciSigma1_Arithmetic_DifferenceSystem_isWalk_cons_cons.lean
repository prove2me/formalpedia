-- Prove2me | solution 1 for DeciSigma1.Arithmetic.DifferenceSystem.isWalk_cons_cons
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:38:36.050172+00:00
-- url     : https://prove2.me/submissions/330376fe-2bb1-48ad-a550-0466114550ec

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
theorem _root_.solution {i j : ι} {p : List ι} :
    D.IsWalk (i :: j :: p) ↔ (D.edgeWeight i j).isSome ∧ D.IsWalk (j :: p) :=
  List.isChain_cons_cons
end DeciSigma1.Arithmetic.DifferenceSystem
