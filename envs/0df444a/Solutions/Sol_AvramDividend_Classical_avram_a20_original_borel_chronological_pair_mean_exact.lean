-- Prove2me | solution 1 for AvramDividend.Classical.avram_a20_original_borel_chronological_pair_mean_exact
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T13:00:59.406301+00:00
-- url     : https://prove2.me/submissions/4ff720c4-960a-4fb6-a471-53dffedfb30b
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Data.Nat.Factorial.SuperFactorial
import Mathlib.Probability.Distributions.Poisson.Basic
import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_a20_original_negative_borel_count_poisson_law
import Theorems.Thm_AvramDividend_Classical_avram_a20_original_negative_borel_factorial_integrable
import Theorems.Thm_AvramDividend_Classical_avram_a20_original_borel_factorial_physical_pair_ae
import Theorems.Thm_ProbabilityTheory_integral_factorialMoment_poissonMeasure
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology Nat
noncomputable section
/-- Genuine chronological pair mean from the physical original Borel Poisson count law. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (T : ℝ≥0) (B : Set ℝ)
    (hB : MeasurableSet B) (hNeg : B ⊆ Iio (0 : ℝ)) :
    let S : Ω → Set ℝ≥0 := fun ω =>
      {u : ℝ≥0 | 0 < u ∧ (0 : ℝ≥0) < u ∧ u ≤ T ∧
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0 ∧
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ∈ B}
    let K : Ω → ℕ := fun ω =>
      ((S ω ×ˢ S ω) ∩
        {p : ℝ≥0 × ℝ≥0 | p.1 < p.2}).ncard
    let r : ℝ := ((T : ℝ≥0∞) * X.ν B).toReal
    Integrable (fun ω => 2 * (K ω : ℝ)) P ∧
      (∫ ω, 2 * (K ω : ℝ) ∂P) = r ^ 2 := by
  letI : IsProbabilityMeasure P := X.isProbability
  let N : Ω → ℝ≥0∞ := fun ω =>
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u, X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc 0 T ×ˢ B)
  let S : Ω → Set ℝ≥0 := fun ω =>
    {u : ℝ≥0 | 0 < u ∧ (0 : ℝ≥0) < u ∧ u ≤ T ∧
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0 ∧
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ∈ B}
  let K : Ω → ℕ := fun ω =>
    ((S ω ×ˢ S ω) ∩ {p : ℝ≥0 × ℝ≥0 | p.1 < p.2}).ncard
  let r : ℝ := ((T : ℝ≥0∞) * X.ν B).toReal
  change Integrable (fun ω => 2 * (K ω : ℝ)) P ∧
    (∫ ω, 2 * (K ω : ℝ) ∂P) = r ^ 2
  have hFI : Integrable
      (fun ω => (N ω).toReal * ((N ω).toReal - 1)) P := by
    simpa only [N] using
      (avram_a20_original_negative_borel_factorial_integrable X hFinite T B hB hNeg)
  have hPair : ∀ᵐ ω ∂P,
      (N ω).toReal * ((N ω).toReal - 1) = 2 * (K ω : ℝ) := by
    simpa only [N, S, K] using
      (avram_a20_original_borel_factorial_physical_pair_ae X hFinite T B hB hNeg)
  have hPairI : Integrable (fun ω => 2 * (K ω : ℝ)) P := hFI.congr hPair
  obtain ⟨K₀, rate, hKm, hLaw, hKae, hrate⟩ := by
    simpa only [N] using
      (avram_a20_original_negative_borel_count_poisson_law X hFinite T B hB hNeg)
  have hPairK : ∀ᵐ ω ∂P,
      2 * (K ω : ℝ) = (K₀ ω : ℝ) * ((K₀ ω : ℝ) - 1) := by
    filter_upwards [hPair, hKae] with ω hp hk
    rw [← hk] at hp
    exact hp.symm
  have hPoisson :
      (∫ ω, (K₀ ω : ℝ) * ((K₀ ω : ℝ) - 1) ∂P) =
        (rate : ℝ) ^ 2 := by
    have hm : AEStronglyMeasurable
        (fun n : ℕ => (n : ℝ) * ((n : ℝ) - 1))
        (poissonMeasure rate) := by fun_prop
    calc
      (∫ ω, (K₀ ω : ℝ) * ((K₀ ω : ℝ) - 1) ∂P) =
          (∫ n : ℕ, (n : ℝ) * ((n : ℝ) - 1) ∂poissonMeasure rate) := by
        simpa only [Function.comp_def] using (hLaw.integral_comp hm)
      _ = (rate : ℝ) ^ 2 :=
        ProbabilityTheory.integral_factorialMoment_poissonMeasure rate
  refine ⟨hPairI, ?_⟩
  calc
    (∫ ω, 2 * (K ω : ℝ) ∂P) =
        (∫ ω, (K₀ ω : ℝ) * ((K₀ ω : ℝ) - 1) ∂P) :=
      integral_congr_ae hPairK
    _ = (rate : ℝ) ^ 2 := hPoisson
    _ = r ^ 2 := by rw [hrate]
