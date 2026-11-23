-- Prove2me | solution 1 for DedekindZeta.Theta.covolume_idealLattice
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:24:33.498798+00:00
-- url     : https://prove2.me/submissions/8d9c73b6-b6e6-4557-8a96-5b4a5afc988d

import Mathlib
import Definitions.Def_DedekindZeta_PoissonSummation
import Definitions.Def_DedekindZeta_Theta
import Theorems.Thm_DedekindZeta_Theta_gaussVSchwartz_apply
import Theorems.Thm_DedekindZeta_Theta_mixedGaussianSchwartz_apply
import Theorems.Thm_DedekindZeta_Theta_map_toMinkowski_symm_volume
attribute [local simp] DedekindZeta.Theta.gaussVSchwartz_apply
attribute [local simp] DedekindZeta.Theta.mixedGaussianSchwartz_apply

set_option autoImplicit true
open NumberField NumberField.mixedEmbedding NumberField.InfinitePlace
open scoped Real nonZeroDivisors Classical FourierTransform RealInnerProductSpace ContDiff
open DedekindZeta DedekindZeta.Theta
variable (K : Type*) [Field K] [NumberField K]
noncomputable section
open MeasureTheory
namespace DedekindZeta.Theta
theorem _root_.solution (𝔞 : Ideal (𝓞 K)) (hne : 𝔞 ≠ 0) :
    ZLattice.covolume (idealLattice K (𝔞 : FractionalIdeal (𝓞 K)⁰ K))
      = covolume K 𝔞 := by
  classical
  set I : FractionalIdeal (𝓞 K)⁰ K := (𝔞 : FractionalIdeal (𝓞 K)⁰ K) with hI
  have hI0 : I ≠ 0 := by
    rw [hI]; exact_mod_cast (FractionalIdeal.coeIdeal_ne_zero).mpr hne
  set I' : (FractionalIdeal (𝓞 K)⁰ K)ˣ := Units.mk0 I hI0 with hI'
  set M := mixedEmbedding.idealLattice K I' with hM
  set c : ENNReal := ENNReal.ofReal ((2 : ℝ) ^ nrComplexPlaces K) with hc
  haveI : (c • (volume : Measure (mixedSpace K))).IsAddHaarMeasure :=
    MeasureTheory.Measure.IsAddHaarMeasure.smul _ (by simp [hc]) (by simp [hc])
  -- `Λ(𝔞)` is the preimage lattice of `M` under `(toMinkowski K).symm`.
  have hLeq : ZLattice.comap ℝ M (toMinkowski K).symm.toLinearMap = idealLattice K I := by
    apply Submodule.ext
    intro x
    show (toMinkowski K).symm.toLinearMap.restrictScalars ℤ x ∈ M ↔ _
    show (toMinkowski K).symm x ∈ M ↔ _
    rw [hM, mixedEmbedding.mem_idealLattice, mem_idealLattice_iff]
    constructor
    · rintro ⟨a, ha, hax⟩
      have ha' : a ∈ (I : Submodule (𝓞 K) K) := ha
      refine ⟨a, ha', ?_⟩
      show toMinkowski K (mixedEmbedding K a) = x
      rw [hax, ContinuousLinearEquiv.apply_symm_apply]
    · rintro ⟨a, ha, hax⟩
      refine ⟨a, ?_, ?_⟩
      · exact ha
      · have heq : eEmb K a = toMinkowski K (mixedEmbedding K a) := rfl
        rw [← hax, heq, ContinuousLinearEquiv.symm_apply_apply]
  -- `(toMinkowski K).symm` maps `volume` to `c • volume`.
  have hmp : MeasurePreserving (toMinkowski K).symm (volume : Measure (minkowskiSpace K))
      (c • (volume : Measure (mixedSpace K))) :=
    ⟨(toMinkowski K).symm.continuous.measurable, by rw [hc, map_toMinkowski_symm_volume]⟩
  have hcov := ZLattice.covolume_comap M (c • volume) volume hmp
  rw [hLeq] at hcov
  -- `covolume M (c • volume) = c.toReal * covolume M volume`.
  set b := Module.Free.chooseBasis ℤ M with hb
  have hcv1 : ZLattice.covolume M (c • volume)
      = c.toReal * ZLattice.covolume M volume := by
    rw [ZLattice.covolume_eq_measure_fundamentalDomain M (c • volume)
        (ZLattice.isAddFundamentalDomain b (c • volume)),
      ZLattice.covolume_eq_measure_fundamentalDomain M volume
        (ZLattice.isAddFundamentalDomain b volume)]
    rw [MeasureTheory.measureReal_def, MeasureTheory.measureReal_def,
      Measure.smul_apply, smul_eq_mul, ENNReal.toReal_mul]
  rw [hcv1] at hcov
  -- Assemble with Mathlib's unweighted covolume.
  rw [mixedEmbedding.covolume_idealLattice] at hcov
  have hctoReal : c.toReal = (2 : ℝ) ^ nrComplexPlaces K := by
    rw [hc, ENNReal.toReal_ofReal (by positivity)]
  rw [hctoReal] at hcov
  -- `2 ^ r₂ * (absNorm · * (2⁻¹) ^ r₂ * √|d|) = absNorm · * √|d|`.
  have habs : (FractionalIdeal.absNorm (I' : FractionalIdeal (𝓞 K)⁰ K) : ℝ)
      = (Ideal.absNorm 𝔞 : ℝ) := by
    rw [hI', Units.val_mk0, hI, FractionalIdeal.coeIdeal_absNorm]
    push_cast; ring
  rw [hcov, covolume, ← habs]
  rw [show ((2 : ℝ) ^ nrComplexPlaces K)
        * ((FractionalIdeal.absNorm (I' : FractionalIdeal (𝓞 K)⁰ K) : ℝ)
            * (2⁻¹) ^ nrComplexPlaces K * Real.sqrt |(discr K : ℝ)|)
      = (FractionalIdeal.absNorm (I' : FractionalIdeal (𝓞 K)⁰ K) : ℝ)
          * (((2 : ℝ) ^ nrComplexPlaces K) * (2⁻¹) ^ nrComplexPlaces K)
          * Real.sqrt |(discr K : ℝ)| by ring]
  rw [← mul_pow]
  norm_num
end DedekindZeta.Theta
