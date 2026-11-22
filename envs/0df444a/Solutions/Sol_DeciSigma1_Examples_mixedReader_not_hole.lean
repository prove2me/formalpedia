-- Prove2me | solution 1 for DeciSigma1.Examples.mixedReader_not_hole
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T15:09:41.199963+00:00
-- url     : https://prove2.me/submissions/f6e6bc53-17a5-451e-9d32-55b6acdbc4ba

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
theorem _root_.solution : ¬ mixedReader.IsHole ![[0, 0, 0], [0, 0]] := by decide +kernel
end DeciSigma1.Examples
