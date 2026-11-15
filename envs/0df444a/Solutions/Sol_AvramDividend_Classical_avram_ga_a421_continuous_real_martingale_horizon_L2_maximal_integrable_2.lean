-- Prove2me | solution 2 for AvramDividend.Classical.avram_ga_a421_continuous_real_martingale_horizon_L2_maximal_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T00:12:12.906407+00:00
-- url     : https://prove2.me/submissions/bc17f5db-9b1a-4c7e-bdb9-3f512ca4aecc

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ga_a424_continuous_martingale_dyadic_discrete_L2_maximal
import Theorems.Thm_AvramDividend_Classical_avram_ga_a427_dyadic_square_grid_sup_monotone
import Theorems.Thm_AvramDividend_Classical_avram_ga_a429_monotone_L1_uniform_budget_integrable_envelope
import Theorems.Thm_AvramDividend_Classical_avram_ga_a431_continuous_path_dyadic_square_envelope_transfer
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
    (hMart : Martingale M 𝓕 P)
    (hCont : ∀ᵐ ω ∂P, Continuous (fun t : ℝ≥0 => M t ω))
    (T : ℝ≥0)
    (hL2 : Integrable (fun ω => (M T ω)^2) P) :
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
  have hint (k : ℕ) : Integrable (f k) P :=
    (avram_ga_a424_continuous_martingale_dyadic_discrete_L2_maximal
      P 𝓕 M hMart hCont T hL2 k).1
  have hbudget (k : ℕ) : (∫ ω, f k ω ∂P) ≤ K :=
    (avram_ga_a424_continuous_martingale_dyadic_discrete_L2_maximal
      P 𝓕 M hMart hCont T hL2 k).2
  have hmeas (k : ℕ) : Measurable (f k) := by
    dsimp [f]
    apply Finset.measurable_range_sup''
    intro i hi
    exact (((hMart.stronglyAdapted _).mono (𝓕.le _)).measurable).pow_const 2
  have hnonneg (k : ℕ) (ω : Ω) : 0 ≤ f k ω := by
    dsimp [f]
    have h0 := Finset.le_sup'
      (f := fun (i : ℕ) => (M ((i : ℝ≥0) * T / (2^k : ℝ≥0)) ω)^2)
      (Finset.mem_range.mpr (by positivity : 0 < 2^k + 1))
    nlinarith [sq_nonneg (M ((0 : ℝ≥0) * T / (2^k : ℝ≥0)) ω)]
  have hmono (ω : Ω) : Monotone (fun k => f k ω) :=
    avram_ga_a427_dyadic_square_grid_sup_monotone M T ω
  obtain ⟨S,hSint,hS⟩ :=
    avram_ga_a429_monotone_L1_uniform_budget_integrable_envelope
      P f K hK hint hmeas hnonneg hmono hbudget
  refine ⟨S,hSint,?_⟩
  filter_upwards [hS, hCont] with ω hSω hCω
  refine ⟨hSω.1, ?_⟩
  exact avram_ga_a431_continuous_path_dyadic_square_envelope_transfer
    M T ω hCω (S ω) (fun k => hSω.2 k)
