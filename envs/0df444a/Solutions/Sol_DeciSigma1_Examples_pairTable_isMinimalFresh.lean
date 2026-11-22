-- Prove2me | solution 1 for DeciSigma1.Examples.pairTable_isMinimalFresh
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T15:09:56.99586+00:00
-- url     : https://prove2.me/submissions/b360f15a-2041-433e-aa69-7b115c7854ee

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
theorem _root_.solution : IsMinimalFresh pairTable ![[1], []] := by decide +kernel
end DeciSigma1.Examples
