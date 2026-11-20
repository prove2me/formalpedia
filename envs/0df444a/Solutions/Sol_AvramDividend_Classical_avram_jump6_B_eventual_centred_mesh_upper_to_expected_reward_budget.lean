-- Prove2me | solution 1 for AvramDividend.Classical.avram_jump6_B_eventual_centred_mesh_upper_to_expected_reward_budget
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T16:56:29.799423+00:00
-- url     : https://prove2.me/submissions/e4704372-2a6d-4c68-aac1-3873445311c6

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
set_option autoImplicit false

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (F : Ω → ℝ) (M : ℕ → Ω → ℝ) (b : ℝ)
    (hFI : Integrable F P)
    (hMI : ∀ j, Integrable (M j) P)
    (hMzero : ∀ j, (∫ ω, M j ω ∂P) = 0)
    (hUpper : ∀ ε : ℝ, 0 < ε →
      ∀ᶠ j in atTop,
        ∀ᵐ ω ∂P, F ω ≤ b + M j ω + ε) :
    (∫ ω, F ω ∂P) ≤ b := by
  by_contra hn
  have hb : b < ∫ ω, F ω ∂P := lt_of_not_ge hn
  let ε : ℝ := ((∫ ω, F ω ∂P) - b) / 2
  have hε : 0 < ε := by dsimp [ε]; linarith
  obtain ⟨j, hj⟩ := (hUpper ε hε).exists
  have hInt : Integrable (fun ω => b + M j ω + ε) P :=
    ((integrable_const b).add (hMI j)).add (integrable_const ε)
  have hMono := integral_mono_ae hFI hInt hj
  have hEq : (∫ ω, b + M j ω + ε ∂P) =
      b + (∫ ω, M j ω ∂P) + ε := by
    calc
      _ = (∫ ω, b + M j ω ∂P) + (∫ _ : Ω, ε ∂P) := by
        exact integral_add ((integrable_const b).add (hMI j)) (integrable_const ε)
      _ = b + (∫ ω, M j ω ∂P) + ε := by
        have hPair : (∫ ω, b + M j ω ∂P) =
            (∫ _ : Ω, b ∂P) + (∫ ω, M j ω ∂P) :=
          integral_add (integrable_const b) (hMI j)
        rw [hPair]
        simp
  rw [hEq, hMzero j] at hMono
  dsimp [ε] at hMono
  linarith
