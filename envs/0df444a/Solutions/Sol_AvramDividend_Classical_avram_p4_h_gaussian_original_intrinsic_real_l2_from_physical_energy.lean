-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_h_gaussian_original_intrinsic_real_l2_from_physical_energy
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T10:45:12.617366+00:00
-- url     : https://prove2.me/submissions/b4b81d1f-88e0-4634-b9c4-0d32591d3215

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The source Fatou estimate gives an actual Bochner L² moment on the
original probability measure once physical square measurability and
the original Lévy band's finite real quadratic energy are verified. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0) (n m : ℕ)
    (hSourceEnergy : IntegrableOn (fun z : ℝ => z ^ 2)
      (Ioc (-(1 / (((min n m : ℕ) : ℝ) + 1)))
           (-(1 / (((max n m : ℕ) : ℝ) + 1)))) X.ν)
    (hSquareAE : AEStronglyMeasurable (fun ω : Ω =>
      (avram_p4_h_gaussian_intrinsic_small_band_compensated X n T ω -
       avram_p4_h_gaussian_intrinsic_small_band_compensated X m T ω) ^ 2) P)
    (hPhysicalEnergy :
      (∫⁻ ω, ENNReal.ofReal
        ((avram_p4_h_gaussian_intrinsic_small_band_compensated X n T ω -
          avram_p4_h_gaussian_intrinsic_small_band_compensated X m T ω) ^ 2) ∂P) ≤
        (T : ℝ≥0∞) *
          (∫⁻ z in Ioc
            (-(1 / (((min n m : ℕ) : ℝ) + 1)))
            (-(1 / (((max n m : ℕ) : ℝ) + 1))),
            ENNReal.ofReal (z ^ 2) ∂X.ν)) :
    Integrable (fun ω : Ω =>
      (avram_p4_h_gaussian_intrinsic_small_band_compensated X n T ω -
       avram_p4_h_gaussian_intrinsic_small_band_compensated X m T ω) ^ 2) P ∧
    (∫ ω : Ω,
      (avram_p4_h_gaussian_intrinsic_small_band_compensated X n T ω -
       avram_p4_h_gaussian_intrinsic_small_band_compensated X m T ω) ^ 2 ∂P) ≤
      (T : ℝ) * (∫ z in Ioc
        (-(1 / (((min n m : ℕ) : ℝ) + 1)))
        (-(1 / (((max n m : ℕ) : ℝ) + 1))), z ^ 2 ∂X.ν) := by
  let C : Set ℝ := Ioc (-(1 / (((min n m : ℕ) : ℝ) + 1)))
                         (-(1 / (((max n m : ℕ) : ℝ) + 1)))
  let f : Ω → ℝ := fun ω =>
    (avram_p4_h_gaussian_intrinsic_small_band_compensated X n T ω -
      avram_p4_h_gaussian_intrinsic_small_band_compensated X m T ω) ^ 2
  change IntegrableOn (fun z : ℝ => z ^ 2) C X.ν at hSourceEnergy
  change AEStronglyMeasurable f P at hSquareAE
  change (∫⁻ ω, ENNReal.ofReal (f ω) ∂P) ≤
    (T : ℝ≥0∞) * (∫⁻ z in C, ENNReal.ofReal (z ^ 2) ∂X.ν) at hPhysicalEnergy
  change Integrable f P ∧ (∫ ω, f ω ∂P) ≤
    (T : ℝ) * (∫ z in C, z ^ 2 ∂X.ν)
  have hNNz : 0 ≤ᵐ[X.ν.restrict C] (fun z : ℝ => z ^ 2) :=
    Filter.Eventually.of_forall (fun z => sq_nonneg z)
  have hEnergyEq : ENNReal.ofReal (∫ z in C, z ^ 2 ∂X.ν) =
      ∫⁻ z in C, ENNReal.ofReal (z ^ 2) ∂X.ν :=
    ofReal_integral_eq_lintegral_ofReal hSourceEnergy hNNz
  have hCapEq : ENNReal.ofReal
      ((T : ℝ) * (∫ z in C, z ^ 2 ∂X.ν)) =
      (T : ℝ≥0∞) * (∫⁻ z in C, ENNReal.ofReal (z ^ 2) ∂X.ν) := by
    rw [ENNReal.ofReal_mul (by positivity), hEnergyEq]
    simp
  have hNNf : 0 ≤ᵐ[P] f :=
    Filter.Eventually.of_forall (by intro ω; dsimp [f]; positivity)
  have hFinite : (∫⁻ ω, ENNReal.ofReal (f ω) ∂P) < ⊤ := by
    calc
      _ ≤ (T : ℝ≥0∞) * (∫⁻ z in C, ENNReal.ofReal (z ^ 2) ∂X.ν) :=
        hPhysicalEnergy
      _ = ENNReal.ofReal ((T : ℝ) * (∫ z in C, z ^ 2 ∂X.ν)) :=
        hCapEq.symm
      _ < ⊤ := ENNReal.ofReal_lt_top
  have hInt : Integrable f P :=
    ⟨hSquareAE, (hasFiniteIntegral_iff_ofReal hNNf).2 hFinite⟩
  have hRNonneg : 0 ≤ (T : ℝ) * (∫ z in C, z ^ 2 ∂X.ν) :=
    mul_nonneg (by positivity) (integral_nonneg (fun z => sq_nonneg z))
  refine ⟨hInt, ?_⟩
  apply (ENNReal.ofReal_le_ofReal_iff hRNonneg).mp
  calc
    ENNReal.ofReal (∫ ω, f ω ∂P) =
      ∫⁻ ω, ENNReal.ofReal (f ω) ∂P :=
        ofReal_integral_eq_lintegral_ofReal hInt hNNf
    _ ≤ (T : ℝ≥0∞) * (∫⁻ z in C, ENNReal.ofReal (z ^ 2) ∂X.ν) :=
        hPhysicalEnergy
    _ = ENNReal.ofReal ((T : ℝ) * (∫ z in C, z ^ 2 ∂X.ν)) :=
        hCapEq.symm
