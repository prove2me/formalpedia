-- Prove2me | solution 1 for BookProof.NsScalarVectorCurry.ae_tendsto_zero_of_tsum_lintegral_ne_top
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T08:20:20.633316+00:00
-- url     : https://prove2.me/submissions/10671ab6-249c-4958-a6c0-ff29af1841b9

-- Generated from ChapterNsScalarVectorCurry.lean — solution of BookProof.NsScalarVectorCurry.ae_tendsto_zero_of_tsum_lintegral_ne_top
import Mathlib
import Definitions.Def_ChapterNsScalarVectorCurry
open BookProof.NsScalarVectorCurry



open MeasureTheory Filter Set
open scoped ENNReal ComplexConjugate


noncomputable section

variable {V W : Type*} [MeasurableSpace V] [MeasurableSpace W]
  {μ : Measure V} {ν : Measure W}

variable {V W : Type*} [MeasurableSpace V] [MeasurableSpace W]
  {μ : Measure V} {ν : Measure W}
variable [SigmaFinite μ] [SigmaFinite ν]

set_option maxHeartbeats 1000000 in
theorem solution {X : Type*} [MeasurableSpace X] {ρ : Measure X}
    (ψ : ℕ → X → ℝ≥0∞) (hmeas : ∀ k, AEMeasurable (ψ k) ρ)
    (h : ∑' k, ∫⁻ x, ψ k x ∂ρ ≠ ∞) :
    ∀ᵐ x ∂ρ, Filter.Tendsto (fun k => ψ k x) Filter.atTop (nhds 0) := by

  have h1 : ∫⁻ x, ∑' k, ψ k x ∂ρ = ∑' k, ∫⁻ x, ψ k x ∂ρ := lintegral_tsum hmeas
  have h2 : ∀ᵐ x ∂ρ, (∑' k, ψ k x) < ∞ :=
    ae_lt_top' (AEMeasurable.ennreal_tsum hmeas) (by rw [h1]; exact h)
  filter_upwards [h2] with x hx
  exact ENNReal.tendsto_atTop_zero_of_tsum_ne_top hx.ne
