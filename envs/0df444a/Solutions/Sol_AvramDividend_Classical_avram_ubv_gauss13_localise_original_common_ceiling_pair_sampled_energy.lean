-- Prove2me | solution 1 for AvramDividend.Classical.avram_ubv_gauss13_localise_original_common_ceiling_pair_sampled_energy
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-09T09:02:22.974513+00:00
-- url     : https://prove2.me/submissions/74586383-c316-4c18-9217-1fb5eb730fc3

import Mathlib.Probability.Process.Stopping
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_gauss13_localise_two_physical_clocks_common_ceiling_pair
import Theorems.Thm_AvramDividend_Classical_avram_ubv_gauss13_localise_original_sampled_stop_gaussian_energy_lintegral

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (τ ρ : Ω → ℝ≥0) (hτρ : ∀ ω, τ ω ≤ ρ ω)
    (ε : ℝ≥0) (hGap : ∀ ω, ρ ω ≤ τ ω + ε)
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
    (Kτ Kρ : Ω → ℕ)
    (hKτ : IsStoppingTime 𝓖 (fun ω => (Kτ ω : WithTop ℕ)))
    (hKρ : IsStoppingTime 𝓖 (fun ω => (Kρ ω : WithTop ℕ)))
    (δ : ℝ≥0)
    (hCeilτ : ∀ ω, τ ω ≤ grid (Kτ ω) ∧ grid (Kτ ω) ≤ τ ω + δ)
    (hCeilρ : ∀ ω, ρ ω ≤ grid (Kρ ω) ∧ grid (Kρ ω) ≤ ρ ω + δ)
    (N : ℕ) (hBound : ∀ ω, max (Kτ ω) (Kρ ω) ≤ N)
    (hTimeA : Integrable (stoppedValue
      (fun i : ℕ => fun _ : Ω => (grid i : ℝ) * X.σ ^ 2)
      (fun ω => ((min (Kτ ω) (Kρ ω)) : WithTop ℕ))) P)
    (hTimeB : Integrable (stoppedValue
      (fun i : ℕ => fun _ : Ω => (grid i : ℝ) * X.σ ^ 2)
      (fun ω => ((max (Kτ ω) (Kρ ω)) : WithTop ℕ))) P) :
    (∫⁻ ω, ENNReal.ofReal
      (((X.X (grid (max (Kτ ω) (Kρ ω))) ω -
          (grid (max (Kτ ω) (Kρ ω)) : ℝ) * X.c) -
        (X.X (grid (min (Kτ ω) (Kρ ω))) ω -
          (grid (min (Kτ ω) (Kρ ω)) : ℝ) * X.c)) ^ 2) ∂P) ≤
      ENNReal.ofReal (((ε : ℝ) + (δ : ℝ)) * X.σ ^ 2) := by
  rcases avram_ubv_gauss13_localise_two_physical_clocks_common_ceiling_pair
      𝓖 τ ρ hτρ ε hGap grid hgrid Kτ Kρ hKτ hKρ δ hCeilτ hCeilρ with
    ⟨hMinStop, hMaxStop, _, _, hPhysical⟩
  let α : Ω → WithTop ℕ := fun ω => (min (Kτ ω) (Kρ ω) : ℕ)
  let β : Ω → WithTop ℕ := fun ω => (max (Kτ ω) (Kρ ω) : ℕ)
  have hαβ : α ≤ β := by
    intro ω
    change ((min (Kτ ω) (Kρ ω) : ℕ) : WithTop ℕ) ≤
      ((max (Kτ ω) (Kρ ω) : ℕ) : WithTop ℕ)
    exact_mod_cast (min_le_max : min (Kτ ω) (Kρ ω) ≤ max (Kτ ω) (Kρ ω))
  have hb : ∀ ω, β ω ≤ (N : WithTop ℕ) := by
    intro ω
    change ((max (Kτ ω) (Kρ ω) : ℕ) : WithTop ℕ) ≤ ((N : ℕ) : WithTop ℕ)
    exact WithTop.coe_le_coe.mpr (hBound ω)
  have ht : ∀ ω,
      stoppedValue (fun i : ℕ => fun _ : Ω => (grid i : ℝ) * X.σ ^ 2) β ω -
      stoppedValue (fun i : ℕ => fun _ : Ω => (grid i : ℝ) * X.σ ^ 2) α ω ≤
      ((ε : ℝ) + (δ : ℝ)) * X.σ ^ 2 := by
    intro ω
    change (grid (max (Kτ ω) (Kρ ω)) : ℝ) * X.σ ^ 2 -
      (grid (min (Kτ ω) (Kρ ω)) : ℝ) * X.σ ^ 2 ≤
      ((ε : ℝ) + (δ : ℝ)) * X.σ ^ 2
    nlinarith [mul_le_mul_of_nonneg_right (hPhysical ω) (sq_nonneg X.σ)]
  have hE := avram_ubv_gauss13_localise_original_sampled_stop_gaussian_energy_lintegral
      X hν grid hgrid 𝓖 h𝓖 α β hMinStop hMaxStop hαβ N hb
      ((ε : ℝ) + (δ : ℝ)) hTimeA hTimeB ht
  exact hE
