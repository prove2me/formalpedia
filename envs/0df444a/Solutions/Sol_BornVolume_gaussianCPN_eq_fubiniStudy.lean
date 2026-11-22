-- Prove2me | solution 1 for BornVolume.gaussianCPN_eq_fubiniStudy
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:07:31.396296+00:00
-- url     : https://prove2.me/submissions/a957c62c-c21a-4dc9-8d78-eaa03fc538e3

module
public import Definitions.Def_BornVolumeLean_Volume_GaussianFS
public import Definitions.Def_BornVolumeLean_LinearAlgebra_Projectivization_UnitaryTransitive
public import Mathlib.Probability.Distributions.Gaussian.Multivariate
public import Mathlib.Probability.Distributions.Gaussian.Fernique
public import Definitions.Def_BornVolumeLean_Volume_GaussianCPN
public import Theorems.Thm_BornVolume_gaussianCPN_smul_invariant
public import Theorems.Thm_Matrix_UnitaryGroup_fsMeasure_unique


set_option autoImplicit false
@[expose] public section
public section
open MeasureTheory ProbabilityTheory Matrix Matrix.UnitaryGroup
open scoped LinearAlgebra.Projectivization
open BornVolume
variable {N : ℕ}
namespace BornVolume
theorem _root_.solution [NeZero N] (p₀ : CPN N) :
    gaussianCPN p₀ = fsMeasure p₀ :=
  fsMeasure_unique p₀ (gaussianCPN p₀) (gaussianCPN_smul_invariant p₀)
end BornVolume
