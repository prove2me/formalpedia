-- Prove2me | solution 1 for GaussianPerimeter.VolumeComparison.iSup_rpow_of_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T11:19:34.21375+00:00
-- url     : https://prove2.me/submissions/065f87dc-d214-4ec7-bab8-2fb60c1b0be0

module
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Definitions.Def_GaussianPerimeter_PrekopaHelpers

set_option autoImplicit true
@[expose] public section
public section
open GaussianPerimeter GaussianPerimeter.VolumeComparison
namespace GaussianPerimeter.VolumeComparison
theorem _root_.solution {ι : Sort*} {r : ℝ} (hr : r > 0) (f : ι → ENNReal) :
    (⨆ (i : ι), f i) ^ r = ⨆ (i : ι), f i ^ r :=
  (ENNReal.orderIsoRpow r hr).map_iSup f
end GaussianPerimeter.VolumeComparison
