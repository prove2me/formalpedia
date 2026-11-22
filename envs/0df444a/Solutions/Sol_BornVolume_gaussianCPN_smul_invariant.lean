-- Prove2me | solution 1 for BornVolume.gaussianCPN_smul_invariant
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:06:45.971063+00:00
-- url     : https://prove2.me/submissions/3e796713-fd06-43c5-8157-4d4ae3b28542

module
public import Definitions.Def_BornVolumeLean_Volume_GaussianFS
public import Definitions.Def_BornVolumeLean_LinearAlgebra_Projectivization_UnitaryTransitive
public import Mathlib.Probability.Distributions.Gaussian.Multivariate
public import Mathlib.Probability.Distributions.Gaussian.Fernique
public import Definitions.Def_BornVolumeLean_Volume_GaussianCPN
public import Theorems.Thm_BornVolume_measurable_toEuclideanLinN
public import Theorems.Thm_BornVolume_gaussianHN_map_unitary
public import Theorems.Thm_BornVolume_gaussianHN_singleton_zero

set_option autoImplicit false
@[expose] public section
public section
open MeasureTheory ProbabilityTheory Matrix Matrix.UnitaryGroup
open scoped LinearAlgebra.Projectivization
open BornVolume
variable {N : ℕ}
namespace BornVolume
theorem _root_.solution [NeZero N] (p₀ : CPN N) (U : Matrix.unitaryGroup (Fin N) ℂ) :
    Measure.map (fun p => U • p) (gaussianCPN p₀) = gaussianCPN p₀ := by
  unfold gaussianCPN
  rw [Measure.map_map (continuous_const_smul U).measurable (measurable_gaussianProjN p₀)]
  have hae : ((fun p => U • p) ∘ gaussianProjN p₀)
      =ᵐ[gaussianHN] (gaussianProjN p₀ ∘ (Matrix.toEuclideanLin U.val)) := by
    refine ae_iff.mpr ?_
    refine measure_mono_null ?_ gaussianHN_singleton_zero
    intro v hv
    simp only [Set.mem_ofPred_eq, Function.comp_apply] at hv
    by_contra hv0
    simp only [Set.mem_singleton_iff] at hv0
    apply hv
    rw [gaussianProjN, dif_neg hv0, gaussianProjN,
      dif_neg (Matrix.UnitaryGroup.toEuclideanLin_unitary_ne_zero U hv0), smul_mk_eq_mk U v hv0]
  rw [Measure.map_congr hae,
    ← Measure.map_map (measurable_gaussianProjN p₀) (measurable_toEuclideanLinN U),
    gaussianHN_map_unitary U]
end BornVolume
