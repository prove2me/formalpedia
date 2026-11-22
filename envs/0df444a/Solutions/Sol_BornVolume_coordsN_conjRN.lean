-- Prove2me | solution 1 for BornVolume.coordsN_conjRN
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:02:49.877325+00:00
-- url     : https://prove2.me/submissions/f83ba47f-00da-4db4-9519-51ebb60de326

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
theorem _root_.solution (U : Matrix.unitaryGroup (Fin N) ℂ)
    (y : EuclideanSpace ℝ (Fin N × Fin 2)) :
    coordsN (conjRN U y) = (Matrix.toEuclideanLin U.val) (coordsN y) := by
  show coordsN (coordsN.symm ((Matrix.toEuclideanLin U.val) (coordsN y))) = _
  rw [LinearIsometryEquiv.apply_symm_apply]
end BornVolume
