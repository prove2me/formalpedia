-- Prove2me | solution 1 for BornVolume.measurableSet_domainN
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T11:53:07.283806+00:00
-- url     : https://prove2.me/submissions/9411df9e-f1ef-46b7-a0ea-38c38c4810b9

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
theorem _root_.solution : MeasurableSet (domainN (M := M)) := by
  have h1 : MeasurableSet {y : Fin (M + 1) → ℝ | ∀ k, 0 < y (Fin.castSucc k)} := by
    rw [Set.ofPred_forall]
    exact MeasurableSet.iInter fun k => measurableSet_lt measurable_const (measurable_pi_apply _)
  have hsum : Measurable (fun y : Fin (M + 1) → ℝ => ∑ k, y (Fin.castSucc k)) :=
    Finset.measurable_sum Finset.univ fun k _ => measurable_pi_apply _
  refine h1.inter (.inter (measurableSet_lt hsum measurable_const)
    (measurableSet_lt measurable_const (measurable_pi_apply _)))
end BornVolume
