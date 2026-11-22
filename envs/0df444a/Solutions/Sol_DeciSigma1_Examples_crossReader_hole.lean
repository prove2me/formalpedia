-- Prove2me | solution 1 for DeciSigma1.Examples.crossReader_hole
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T15:07:14.491198+00:00
-- url     : https://prove2.me/submissions/93abf030-5226-465d-aad4-d5d00d4ee340

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
theorem _root_.solution : crossReader.IsHole ![[], [0]] := by decide +kernel
end DeciSigma1.Examples
