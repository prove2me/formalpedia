-- Prove2me | solution 1 for DeciSigma1.Examples.mixedReader_hasMixedMortality
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T15:09:15.289069+00:00
-- url     : https://prove2.me/submissions/e583a583-87ff-4b22-8169-688da41c7553

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
theorem _root_.solution : mixedReader.HasMixedMortality mixedWords := by
  decide +kernel
end DeciSigma1.Examples
