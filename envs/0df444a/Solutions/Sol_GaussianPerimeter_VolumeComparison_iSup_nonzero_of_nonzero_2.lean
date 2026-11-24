-- Prove2me | solution 2 for GaussianPerimeter.VolumeComparison.iSup_nonzero_of_nonzero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T11:19:02.50454+00:00
-- url     : https://prove2.me/submissions/35c08d60-c441-44f4-8e90-36da188fdc48

module
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Definitions.Def_GaussianPerimeter_PrekopaHelpers

set_option autoImplicit true
@[expose] public section
public section
open GaussianPerimeter GaussianPerimeter.VolumeComparison
namespace GaussianPerimeter.VolumeComparison
theorem _root_.solution {f : ℝ → ENNReal} (hf_nonzero : f ≠ 0) : iSup f ≠ 0 := by
  intro h
  apply hf_nonzero
  ext x
  simpa using le_iSup f x |>.trans_eq h
end GaussianPerimeter.VolumeComparison
