-- Prove2me | solution 1 for BornVolume.psiFDerivN_det
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T11:54:35.748218+00:00
-- url     : https://prove2.me/submissions/01dbc3e4-a1f9-4cd2-a9e4-d339f9bb34bd

module
public import Mathlib.MeasureTheory.Function.Jacobian
public import Mathlib.MeasureTheory.Integral.Gamma
public import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.LinearAlgebra.Matrix.Block
public import Definitions.Def_BornVolumeLean_Volume_MomentMarginalUniform
public import Definitions.Def_BornVolumeLean_MeasureTheory_LintegralFintypeProd
public import Definitions.Def_BornVolumeLean_Volume_MomentRatioUniformN
public import Theorems.Thm_BornVolume_psiMat_det

set_option autoImplicit false
@[expose] public section
public section
open MeasureTheory Real Set
open scoped ENNReal
open BornVolume
variable {M : ℕ}
namespace BornVolume
theorem _root_.solution (y : Fin (M + 1) → ℝ) :
    (psiFDerivN y).det = (y (Fin.last M)) ^ M := by
  rw [psiFDerivN, ContinuousLinearMap.det, LinearMap.coe_toContinuousLinearMap,
    LinearMap.det_toLin', psiMat_det]
end BornVolume
