-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a59_positive_energy_uniform_bound_large_tail_to_L1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T07:37:14.049967+00:00
-- url     : https://prove2.me/submissions/9055cc39-93bb-45d3-8a48-6f92ca669ee9

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic.Positivity
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- A uniformly bounded quadratic-energy budget and vanishing rare-increment tails force positive Taylor L1 error to zero. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (A E : ℕ → Ω → ℝ) (T : ℕ → ℕ → Ω → ℝ)
    (K : ℝ) (hK : 0 ≤ K)
    (hAInt : ∀ m, Integrable (A m) P)
    (hApos : ∀ m ω, 0 ≤ A m ω)
    (hEbound : ∀ m, (∫ ω, E m ω ∂P) ≤ K)
    (hModulus : ∀ η : ℝ, 0 < η →
      ∃ j : ℕ, ∃ M : ℝ, 0 ≤ M ∧
        ∀ m, (∫ ω, A m ω ∂P) ≤
          η * (∫ ω, E m ω ∂P) +
            M * (∫ ω, T j m ω ∂P))
    (hTail : ∀ j : ℕ, Tendsto
      (fun m : ℕ => ∫ ω, T j m ω ∂P) atTop (𝓝 (0 : ℝ))) :
    Tendsto (fun m : ℕ => ∫ ω, A m ω ∂P) atTop (𝓝 (0 : ℝ)) := by
  refine tendsto_order.mpr ⟨?_, ?_⟩
  · intro a ha
    exact Filter.Eventually.of_forall (fun m =>
      lt_of_lt_of_le ha (integral_nonneg (hApos m)))
  · intro b hb
    have hEta : 0 < b / (2 * (K + 1)) := by positivity
    obtain ⟨j, M, hM, hBound⟩ := hModulus _ hEta
    have hScaled : Tendsto
        (fun m => M * (∫ ω, T j m ω ∂P))
        atTop (𝓝 (0 : ℝ)) := by
      simpa only [mul_zero] using (hTail j).const_mul M
    have hEvent : ∀ᶠ m in atTop,
        M * (∫ ω, T j m ω ∂P) < b / 2 :=
      hScaled.eventually_lt_const (by linarith)
    have hFraction : b / (2 * (K + 1)) * K ≤ b / 2 := by
      have hDen : 0 < K + 1 := by linarith
      have hRatio : K / (K + 1) ≤ 1 := by
        apply (div_le_iff₀ hDen).2
        linarith
      calc
        b / (2 * (K + 1)) * K =
            (b / 2) * (K / (K + 1)) := by
          field_simp [ne_of_gt hDen]
        _ ≤ (b / 2) * 1 :=
          mul_le_mul_of_nonneg_left hRatio (by linarith)
        _ = b / 2 := by ring
    filter_upwards [hEvent] with m hm
    have hBudget :
        (b / (2 * (K + 1))) * (∫ ω, E m ω ∂P) ≤
          b / (2 * (K + 1)) * K :=
      mul_le_mul_of_nonneg_left (hEbound m) hEta.le
    calc
      (∫ ω, A m ω ∂P) ≤
          b / (2 * (K + 1)) * (∫ ω, E m ω ∂P) +
            M * (∫ ω, T j m ω ∂P) := hBound m
      _ ≤ b / (2 * (K + 1)) * K +
            M * (∫ ω, T j m ω ∂P) :=
        add_le_add hBudget (le_refl _)
      _ < b / 2 + b / 2 :=
        add_lt_add_of_le_of_lt hFraction hm
      _ = b := by ring
