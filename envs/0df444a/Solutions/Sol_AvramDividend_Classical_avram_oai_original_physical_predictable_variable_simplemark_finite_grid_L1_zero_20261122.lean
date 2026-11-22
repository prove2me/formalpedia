-- Prove2me | solution 1 for AvramDividend.Classical.avram_oai_original_physical_predictable_variable_simplemark_finite_grid_L1_zero_20261122
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T17:15:34.534884+00:00
-- url     : https://prove2.me/submissions/e4320b3c-183f-46c4-9d94-167a07d9fa37

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_oai_original_physical_simple_signed_mark_predictable_weight_condExp_zero_allactivity_20261122
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
set_option autoImplicit false

theorem solution
    {Ω ι : Type*} [mΩ : MeasurableSpace Ω] [DecidableEq ι]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (F : Finset ι) (s t : ι → ℝ≥0)
    (hst : ∀ i ∈ F, s i < t i)
    (S : ι → Set ℝ)
    (hS : ∀ i ∈ F, MeasurableSet (S i))
    (hNeg : ∀ i ∈ F, S i ⊆ Iio (0 : ℝ))
    (hν : ∀ i ∈ F, X.ν (S i) < ⊤)
    (g : ι → SimpleFunc ℝ ℝ)
    (H : ι → Ω → ℝ)
    (hH : ∀ i ∈ F,
      StronglyMeasurable[𝓕.rightCont (s i)] (H i)) :
    let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
    let B : ι → ℝ → Set ℝ := fun i y => S i ∩ (g i) ⁻¹' {y}
    let G : ι → Ω → ℝ := fun i ω =>
      ∑ y ∈ (g i).range, y *
        ((NX ω (Ioc (s i) (t i) ×ˢ B i y)).toReal -
          ((((t i - s i : ℝ≥0) : ℝ≥0∞) * X.ν (B i y))).toReal)
    (∀ i ∈ F, Integrable (fun ω => H i ω * G i ω) P) →
      Integrable (fun ω => ∑ i ∈ F, H i ω * G i ω) P ∧
        (∫ ω, ∑ i ∈ F, H i ω * G i ω ∂P) = 0  := by
  classical
  intro NX B G hHI
  have hEach : ∀ i ∈ F,
      (∫ ω, H i ω * G i ω ∂P) = 0 := by
    intro i hi
    have hZero :=
      avram_oai_original_physical_simple_signed_mark_predictable_weight_condExp_zero_allactivity_20261122
        X (s i) (t i) (hst i hi) (S i) (hS i hi)
          (hNeg i hi) (hν i hi) (g i)
          (H i) (hH i hi) (hHI i hi)
    have hCond : P[(fun ω => H i ω * G i ω) | 𝓕.rightCont (s i)] =ᵐ[P]
        (fun _ => (0 : ℝ)) := by
      simpa only [NX, B, G] using hZero
    calc
      (∫ ω, H i ω * G i ω ∂P) =
        (∫ ω, P[(fun η => H i η * G i η) |
          𝓕.rightCont (s i)] ω ∂P) :=
        (integral_condExp (𝓕.rightCont.le (s i))).symm
      _ = (∫ ω, (0 : ℝ) ∂P) := integral_congr_ae hCond
      _ = 0 := by simp
  have hSum : Integrable (fun ω =>
      ∑ i ∈ F, H i ω * G i ω) P :=
    integrable_finset_sum F (fun i hi => hHI i hi)
  refine ⟨hSum, ?_⟩
  rw [integral_finset_sum F (fun i hi => hHI i hi)]
  exact Finset.sum_eq_zero (fun i hi => hEach i hi)
