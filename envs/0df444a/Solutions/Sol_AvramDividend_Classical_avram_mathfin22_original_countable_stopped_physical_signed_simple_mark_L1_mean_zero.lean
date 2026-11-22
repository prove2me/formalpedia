-- Prove2me | solution 1 for AvramDividend.Classical.avram_mathfin22_original_countable_stopped_physical_signed_simple_mark_L1_mean_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T17:02:59.910855+00:00
-- url     : https://prove2.me/submissions/7b1f27c5-8e85-4402-903a-387306a4a5e5

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_oai_original_actual_simple_negative_mark_countable_stop_mean_zero_unconditional_20261122
import Theorems.Thm_AvramDividend_Classical_avram_mathfin22_original_local_simple_compensated_fibre_identity
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
set_option autoImplicit false

/-- The true original compensated signed mark integral is stopped and centred. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (T : ℝ≥0) (n : ℕ)
    (S : Set ℝ) (hS : MeasurableSet S)
    (hNeg : S ⊆ Iio (0 : ℝ))
    (hSep : S ⊆ Iic (-(1 / ((n : ℝ) + 1))))
    (hν : X.ν S < ⊤)
    (g : SimpleFunc ℝ ℝ) (hBound : ∀ z ∈ S, |g z| ≤ 1)
    (τ : Ω → WithTop ℝ≥0)
    (hτ : IsStoppingTime 𝓕.rightCont τ)
    (hτbound : ∀ ω, τ ω ≤ (T : WithTop ℝ≥0))
    (hτcount : (Set.range τ).Countable) :
    let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
    let R : Ω → ℝ := fun ω =>
      (∫ p in Ioc 0 (τ ω).untopA ×ˢ S, g p.2 ∂(NX ω)) -
        (((τ ω).untopA : ℝ) * (∫ z in S, g z ∂X.ν))
    Integrable R P ∧ (∫ ω, R ω ∂P) = 0 := by
  classical
  intro NX R
  let B : ℝ → Set ℝ := fun y => S ∩ g ⁻¹' {y}
  let F : ℝ≥0 → Ω → ℝ := fun t ω =>
    ∑ y ∈ g.range, y *
      ((NX ω (Ioc 0 t ×ˢ B y)).toReal -
        (((t : ℝ≥0∞) * X.ν (B y))).toReal)
  have hMartStop :
      Integrable (stoppedValue F τ) P ∧
      (∫ ω, stoppedValue F τ ω ∂P) = 0 := by
    simpa only [F, B, NX] using
      (avram_oai_original_actual_simple_negative_mark_countable_stop_mean_zero_unconditional_20261122
        X S hS hNeg hν g T τ hτ hτbound hτcount)
  have hId : ∀ ω, stoppedValue F τ ω = R ω := by
    intro ω
    simpa only [stoppedValue, F, B, NX, R] using
      (avram_mathfin22_original_local_simple_compensated_fibre_identity
        X (τ ω).untopA n S hS hSep g hBound ω)
  have hEq : stoppedValue F τ =ᵐ[P] R :=
    Filter.Eventually.of_forall hId
  refine ⟨hMartStop.1.congr hEq, ?_⟩
  calc
    (∫ ω, R ω ∂P) = (∫ ω, stoppedValue F τ ω ∂P) :=
      integral_congr_ae hEq.symm
    _ = 0 := hMartStop.2
