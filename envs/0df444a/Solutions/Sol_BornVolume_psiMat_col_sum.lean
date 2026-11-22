-- Prove2me | solution 1 for BornVolume.psiMat_col_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T11:53:01.666797+00:00
-- url     : https://prove2.me/submissions/6aee3e4e-1dd4-419b-8514-78112ade1ef6

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
theorem _root_.solution (S : ℝ) (t : Fin M → ℝ) (j : Fin (M + 1)) :
    ∑ i, psiMat S t i j = if j = Fin.last M then (1 : ℝ) else 0 := by
  rw [Fin.sum_univ_castSucc]
  simp only [psiMat, Matrix.of_apply, Fin.lastCases_castSucc, Fin.lastCases_last]
  induction j using Fin.lastCases with
  | last =>
    simp only [Fin.lastCases_last, ite_true]
    abel
  | cast a =>
    simp only [Fin.lastCases_castSucc, if_neg (Fin.castSucc_ne_last a)]
    rw [Finset.sum_eq_single a]
    · simp
    · intro b _ hb; simp [hb]
    · intro h; exact absurd (Finset.mem_univ a) h
end BornVolume
