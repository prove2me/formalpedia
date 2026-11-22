-- Prove2me | solution 1 for BornVolume.gaussianHN_map_unitary
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:04:28.391921+00:00
-- url     : https://prove2.me/submissions/4415ba8b-7319-4fdb-889b-6b30d34eb3b8

module
public import Definitions.Def_BornVolumeLean_Volume_GaussianFS
public import Definitions.Def_BornVolumeLean_LinearAlgebra_Projectivization_UnitaryTransitive
public import Mathlib.Probability.Distributions.Gaussian.Multivariate
public import Mathlib.Probability.Distributions.Gaussian.Fernique
public import Definitions.Def_BornVolumeLean_Volume_GaussianCPN
public import Theorems.Thm_BornVolume_measurable_toEuclideanLinN
public import Theorems.Thm_BornVolume_coordsN_conjRN

set_option autoImplicit false
@[expose] public section
public section
open MeasureTheory ProbabilityTheory Matrix Matrix.UnitaryGroup
open scoped LinearAlgebra.Projectivization
open BornVolume
variable {N : ℕ}
namespace BornVolume
theorem _root_.solution (U : Matrix.unitaryGroup (Fin N) ℂ) :
    Measure.map (Matrix.toEuclideanLin U.val) gaussianHN = gaussianHN := by
  unfold gaussianHN
  rw [Measure.map_map (measurable_toEuclideanLinN U) coordsN.continuous.measurable]
  have hcomp : (Matrix.toEuclideanLin U.val) ∘ coordsN = coordsN ∘ (conjRN U) := by
    funext y
    simp only [Function.comp_apply, coordsN_conjRN]
  rw [hcomp, ← Measure.map_map coordsN.continuous.measurable (conjRN U).continuous.measurable,
    stdGaussian_map (conjRN U)]
end BornVolume
