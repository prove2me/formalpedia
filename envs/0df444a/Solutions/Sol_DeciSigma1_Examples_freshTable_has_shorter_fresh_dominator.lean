-- Prove2me | solution 1 for DeciSigma1.Examples.freshTable_has_shorter_fresh_dominator
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T15:09:41.754204+00:00
-- url     : https://prove2.me/submissions/287aa735-f829-441e-969c-f15c939237e3

module
public import Mathlib.Data.Fin.VecNotation
public import Definitions.Def_LeanPool_DeciSigma1_Full_Reduction_Compile
public import Definitions.Def_LeanPool_DeciSigma1_Examples_Readers

set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Examples
open DeciSigma1.Readers DeciSigma1.Constraints DeciSigma1.Full DeciSigma1.Full.Reduction
namespace DeciSigma1.Examples
theorem _root_.solution : FreshDominates freshTable ![[1]] ![[0, 1]] ∧
    totalLength ![[1]] < totalLength (![[0, 1]] : Fin 1 → List (Fin 2)) := by decide +kernel
end DeciSigma1.Examples
