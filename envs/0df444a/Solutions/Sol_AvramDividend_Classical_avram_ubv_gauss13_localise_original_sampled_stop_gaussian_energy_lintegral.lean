-- Prove2me | solution 1 for AvramDividend.Classical.avram_ubv_gauss13_localise_original_sampled_stop_gaussian_energy_lintegral
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-09T08:23:34.87367+00:00
-- url     : https://prove2.me/submissions/e5ad1135-dd64-4102-aed8-0a1400f3047d

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_finite13_original_bounded_stopped_gaussian_L2_integrability
import Theorems.Thm_AvramDividend_Classical_avram_ubv_gauss13_localise_original_two_sampled_stops_gaussian_gap_L2

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (grid : ℕ → ℝ≥0) (hgrid : Monotone grid)
    (𝓖 : Filtration ℕ mΩ) [SigmaFiniteFiltration P 𝓖]
    (h𝓖 : 𝓖 =
      ({ seq := fun i : ℕ => 𝓕.rightCont (grid i)
         mono' := by
           intro i j hij
           exact 𝓕.rightCont.mono (hgrid hij)
         le' := by
           intro i
           exact 𝓕.rightCont.le (grid i) } : Filtration ℕ mΩ))
    (α β : Ω → WithTop ℕ)
    (hα : IsStoppingTime 𝓖 α) (hβ : IsStoppingTime 𝓖 β)
    (hαβ : α ≤ β)
    (N : ℕ) (hbounded : ∀ ω, β ω ≤ (N : WithTop ℕ))
    (ε : ℝ)
    (hTimeA : Integrable (stoppedValue
      (fun i : ℕ => fun _ : Ω => (grid i : ℝ) * X.σ ^ 2) α) P)
    (hTimeB : Integrable (stoppedValue
      (fun i : ℕ => fun _ : Ω => (grid i : ℝ) * X.σ ^ 2) β) P)
    (hGap : ∀ ω,
      stoppedValue
          (fun i : ℕ => fun _ : Ω => (grid i : ℝ) * X.σ ^ 2) β ω -
        stoppedValue
          (fun i : ℕ => fun _ : Ω => (grid i : ℝ) * X.σ ^ 2) α ω
        ≤ ε * X.σ ^ 2) :
    let M : ℝ≥0 → Ω → ℝ := fun t ω =>
      X.X t ω - (t : ℝ) * X.c
    let A := stoppedValue (fun i : ℕ => M (grid i)) α
    let B := stoppedValue (fun i : ℕ => M (grid i)) β
    (∫⁻ ω, ENNReal.ofReal ((B ω - A ω) ^ 2) ∂P) ≤
      ENNReal.ofReal (ε * X.σ ^ 2) := by
  letI : IsProbabilityMeasure P := X.isProbability
  let M : ℝ≥0 → Ω → ℝ := fun t ω =>
    X.X t ω - (t : ℝ) * X.c
  let A := stoppedValue (fun i : ℕ => M (grid i)) α
  let B := stoppedValue (fun i : ℕ => M (grid i)) β
  change (∫⁻ ω, ENNReal.ofReal ((B ω - A ω) ^ 2) ∂P) ≤
    ENNReal.ofReal (ε * X.σ ^ 2)
  have hLp := avram_ubv_finite13_original_bounded_stopped_gaussian_L2_integrability
    X hν grid hgrid 𝓖 h𝓖 α β hα hβ hαβ N hbounded
  have hLpA : MemLp A 2 P := hLp.1
  have hLpB : MemLp B 2 P := hLp.2.1
  have hDiff : MemLp (fun ω => B ω - A ω) 2 P :=
    hLpB.sub hLpA
  have hInt : Integrable (fun ω => (B ω - A ω) ^ 2) P :=
    (memLp_two_iff_integrable_sq hDiff.aestronglyMeasurable).1 hDiff
  have hNonneg : 0 ≤ᵐ[P] fun ω => (B ω - A ω) ^ 2 :=
    Filter.Eventually.of_forall (fun ω => sq_nonneg (B ω - A ω))
  have hConvert := ofReal_integral_eq_lintegral_ofReal hInt hNonneg
  have hBound : (∫ ω, (B ω - A ω) ^ 2 ∂P) ≤ ε * X.σ ^ 2 :=
    avram_ubv_gauss13_localise_original_two_sampled_stops_gaussian_gap_L2
      X hν grid hgrid 𝓖 h𝓖 α β hα hβ hαβ N hbounded
      ε hTimeA hTimeB hGap
  calc
    (∫⁻ ω, ENNReal.ofReal ((B ω - A ω) ^ 2) ∂P) =
      ENNReal.ofReal (∫ ω, (B ω - A ω) ^ 2 ∂P) := hConvert.symm
    _ ≤ ENNReal.ofReal (ε * X.σ ^ 2) :=
      ENNReal.ofReal_le_ofReal hBound
