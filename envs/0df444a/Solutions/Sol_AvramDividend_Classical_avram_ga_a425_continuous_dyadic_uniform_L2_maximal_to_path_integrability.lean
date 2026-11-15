-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a425_continuous_dyadic_uniform_L2_maximal_to_path_integrability
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T00:12:22.941024+00:00
-- url     : https://prove2.me/submissions/24377589-5962-43bc-9a27-329fbe7e0979

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ga_a427_dyadic_square_grid_sup_monotone
import Theorems.Thm_AvramDividend_Classical_avram_ga_a431_continuous_path_dyadic_square_envelope_transfer
import Theorems.Thm_AvramDividend_Classical_avram_ga_a435_ae_monotone_L1_integrable_envelope
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (𝓕 : Filtration ℝ≥0 mΩ)
    (M : ℝ≥0 → Ω → ℝ)
    (hCont : ∀ᵐ ω ∂P, Continuous (fun t : ℝ≥0 => M t ω))
    (T : ℝ≥0)
    (hL2 : Integrable (fun ω => (M T ω)^2) P)     (hDyad : ∀ k : ℕ,
      Integrable (fun ω =>
        (Finset.range (2^k + 1)).sup'
          (by simp) (fun i =>
            (M ((i : ℝ≥0) * T / (2^k : ℝ≥0)) ω)^2)) P ∧
      (∫ ω,
        (Finset.range (2^k + 1)).sup'
          (by simp) (fun i =>
            (M ((i : ℝ≥0) * T / (2^k : ℝ≥0)) ω)^2) ∂P) ≤
        4 * (∫ ω, (M T ω)^2 ∂P)) :
    ∃ S : Ω → ℝ, Integrable S P ∧
      (∀ᵐ ω ∂P, 0 ≤ S ω ∧
        ∀ t : ℝ≥0, t ≤ T → (M t ω)^2 ≤ S ω) := by
  classical
  let f : ℕ → Ω → ℝ := fun k ω =>
    (Finset.range (2^k + 1)).sup' (by simp)
      (fun i => (M ((i : ℝ≥0) * T / (2^k : ℝ≥0)) ω)^2)
  let K : ℝ := 4 * ∫ ω, (M T ω)^2 ∂P
  have hK : 0 ≤ K := by
    dsimp [K]
    have hpositive : 0 ≤ ∫ ω, (M T ω)^2 ∂P :=
      integral_nonneg fun ω => sq_nonneg _
    positivity
  have hint (k : ℕ) : Integrable (f k) P := (hDyad k).1
  have hbudget (k : ℕ) : (∫ ω, f k ω ∂P) ≤ K := (hDyad k).2
  have hnonneg (k : ℕ) (ω : Ω) : 0 ≤ f k ω := by
    dsimp [f]
    have h0 := Finset.le_sup'
      (f := fun (i : ℕ) => (M ((i : ℝ≥0) * T / (2^k : ℝ≥0)) ω)^2)
      (Finset.mem_range.mpr (by positivity : 0 < 2^k + 1))
    nlinarith [sq_nonneg (M ((0 : ℝ≥0) * T / (2^k : ℝ≥0)) ω)]
  have hmono (ω : Ω) : Monotone (fun k => f k ω) :=
    avram_ga_a427_dyadic_square_grid_sup_monotone M T ω
  obtain ⟨S,hSint,hS⟩ :=
    avram_ga_a435_ae_monotone_L1_integrable_envelope
      P f K hK hint hnonneg hmono hbudget
  refine ⟨S,hSint,?_⟩
  filter_upwards [hS, hCont] with ω hSω hCω
  refine ⟨hSω.1, ?_⟩
  exact avram_ga_a431_continuous_path_dyadic_square_envelope_transfer
    M T ω hCω (S ω) (fun k => hSω.2 k)
