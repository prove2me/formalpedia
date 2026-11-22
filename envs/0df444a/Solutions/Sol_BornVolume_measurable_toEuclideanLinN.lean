-- Prove2me | solution 1 for BornVolume.measurable_toEuclideanLinN
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:02:48.372797+00:00
-- url     : https://prove2.me/submissions/fbeb4ba8-9c63-42db-ba6b-7434f1127cf4

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
theorem _root_.solution (U : Matrix.unitaryGroup (Fin N) ℂ) :
    Measurable (Matrix.toEuclideanLin U.val) :=
  (LinearMap.continuous_of_finiteDimensional (Matrix.toEuclideanLin U.val)).measurable
end BornVolume
