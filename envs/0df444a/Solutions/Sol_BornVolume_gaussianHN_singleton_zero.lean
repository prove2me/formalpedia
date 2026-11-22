-- Prove2me | solution 1 for BornVolume.gaussianHN_singleton_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:03:20.316395+00:00
-- url     : https://prove2.me/submissions/bc64958f-d96a-4037-905d-9f189846e24a

module
public import Definitions.Def_BornVolumeLean_Volume_GaussianFS
public import Definitions.Def_BornVolumeLean_LinearAlgebra_Projectivization_UnitaryTransitive
public import Mathlib.Probability.Distributions.Gaussian.Multivariate
public import Mathlib.Probability.Distributions.Gaussian.Fernique
public import Definitions.Def_BornVolumeLean_Volume_GaussianCPN

set_option autoImplicit false
@[expose] public section
public section
open MeasureTheory ProbabilityTheory Matrix Matrix.UnitaryGroup
open scoped LinearAlgebra.Projectivization
open BornVolume
variable {N : ℕ}
namespace BornVolume
theorem _root_.solution [NeZero N] :
    gaussianHN {(0 : EuclideanSpace ℂ (Fin N))} = 0 := by
  unfold gaussianHN
  rw [Measure.map_apply coordsN.continuous.measurable (measurableSet_singleton 0)]
  have : (coordsN ⁻¹' {(0 : EuclideanSpace ℂ (Fin N))})
      = {(0 : EuclideanSpace ℝ (Fin N × Fin 2))} := by
    ext y
    simp only [Set.mem_preimage, Set.mem_singleton_iff, map_eq_zero_iff coordsN coordsN.injective]
  rw [this, measure_singleton]
end BornVolume
