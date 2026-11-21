-- Prove2me | solution 1 for AvramDividend.Classical.avram_agentC_original_random_fullcell_centred_L2_envelope_public
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T21:37:07.521108+00:00
-- url     : https://prove2.me/submissions/bcb59a50-c431-4f9f-b099-20e8352e554b

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ga_a400_zerojump_centred_source_horizon_sup_square_integrable
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsFiniteMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (n : ℕ) (i : ℕ → Ω → ℕ)
    (hEnd : ∀ (m : ℕ) (ω : Ω),
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
      (i m ω : ℝ≥0) * Δ + Δ ≤ (n : ℝ≥0))
    (Z : ℕ → Ω → ℝ)
    (hZeq : ∀ (m : ℕ) (ω : Ω),
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
      let s : ℝ≥0 := (i m ω : ℝ≥0) * Δ
      Z m ω = X.X (s + Δ) ω - X.X s ω - (Δ : ℝ) * X.c)
:
    ∃ B : Ω → ℝ, Integrable B P ∧
      (∀ᵐ ω ∂P, ∀ m,
        |Z m ω| + (Z m ω)^2 +
          ((n : ℝ) / ((m : ℝ) + 1)) ≤ B ω) := by
  obtain ⟨S, hSI, hSbound⟩ :=
    avram_ga_a400_zerojump_centred_source_horizon_sup_square_integrable
      X hν (n : ℝ≥0)
  refine ⟨fun ω => 1 + 8 * S ω + (n : ℝ), ?_, ?_⟩
  · have hBase : Integrable (fun ω => (1 + (n : ℝ)) + 8 * S ω) P :=
      (integrable_const (1 + (n : ℝ))).add (hSI.const_mul 8)
    have hfun : (fun ω => 1 + 8 * S ω + (n : ℝ)) =
        (fun ω => (1 + (n : ℝ)) + 8 * S ω) := by
      funext ω
      ring
    rw [hfun]
    exact hBase
  · filter_upwards [hSbound] with ω hSb
    have hSp : 0 ≤ S ω := hSb.1
    have hSle := hSb.2
    intro m
    let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
    let s : ℝ≥0 := (i m ω : ℝ≥0) * Δ
    have hts : s + Δ ≤ n := hEnd m ω
    have hs : s ≤ (n : ℝ≥0) := le_trans (le_add_of_nonneg_right (by positivity)) hts
    have hsu := hSle s hs
    have htu := hSle (s + Δ) hts
    have hz : (Z m ω)^2 ≤ 4 * S ω := by
      have hZpair : Z m ω =
          (X.X (s + Δ) ω - ((s + Δ : ℝ≥0) : ℝ) * X.c) -
            (X.X s ω - (s : ℝ) * X.c) := by
        rw [hZeq m ω, NNReal.coe_add]
        ring
      rw [hZpair]
      nlinarith [sq_nonneg ((X.X (s + Δ) ω - ((s + Δ : ℝ≥0) : ℝ) * X.c) +
        (X.X s ω - (s : ℝ) * X.c))]
    have hza : |Z m ω| ≤ (Z m ω)^2 + 1 := by
      nlinarith [sq_nonneg (|Z m ω| - 1), sq_abs (Z m ω)]
    have hD : (Δ : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast (le_trans (le_add_of_nonneg_left (by positivity)) hts)
    change |Z m ω| + (Z m ω)^2 + (Δ : ℝ) ≤
      1 + 8 * S ω + (n : ℝ)
    linarith
