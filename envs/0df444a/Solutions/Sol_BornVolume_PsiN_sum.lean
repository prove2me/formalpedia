-- Prove2me | solution 1 for BornVolume.PsiN_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T11:52:09.34186+00:00
-- url     : https://prove2.me/submissions/4032dbe7-4319-4897-a890-b53b1d6e10b2

module
public import Mathlib.MeasureTheory.Function.Jacobian
public import Mathlib.MeasureTheory.Integral.Gamma
public import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.LinearAlgebra.Matrix.Block
public import Definitions.Def_BornVolumeLean_Volume_MomentMarginalUniform
public import Definitions.Def_BornVolumeLean_MeasureTheory_LintegralFintypeProd
public import Definitions.Def_BornVolumeLean_Volume_MomentRatioUniformN

set_option autoImplicit false
@[expose] public section
public section
open MeasureTheory Real Set
open scoped ENNReal
open BornVolume
variable {M : ℕ}
namespace BornVolume
theorem _root_.solution (y : Fin (M + 1) → ℝ) : ∑ i, PsiN y i = y (Fin.last M) := by
  rw [Fin.sum_univ_castSucc]
  simp only [PsiN, Fin.lastCases_castSucc, Fin.lastCases_last]
  rw [← Finset.sum_mul]
  ring
end BornVolume
