-- Prove2me | solution 1 for AvramDividend.Classical.avram_b24_uniform_quadratic_energy_absorption_L1_error_vanish
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T21:10:48.766781+00:00
-- url     : https://prove2.me/submissions/a58a98ef-394b-40dc-9fc4-271bf12a84c7

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology AvramDividend.Classical
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    (Err Energy : ℕ → Ω → ℝ)
    (M : ℝ) (hM : 0 ≤ M)
    (hEnergy : ∀ k, (∫ ω, |Energy k ω| ∂P) ≤ M)
    (hAbsorb : ∀ ε : ℝ, 0 < ε →
      ∃ K : ℕ, ∀ k : ℕ, K ≤ k →
        (∫ ω, |Err k ω| ∂P) ≤
          ε * (∫ ω, |Energy k ω| ∂P)) :
    Tendsto (fun k => ∫ ω, |Err k ω| ∂P)
      atTop (𝓝 (0 : ℝ)) := by
  apply Metric.tendsto_atTop.2
  intro δ hδ
  let η := δ / (M + 1)
  have hden : 0 < M + 1 := by linarith
  have hη : 0 < η := div_pos hδ hden
  obtain ⟨K,hK⟩ := hAbsorb η hη
  refine ⟨K, ?_⟩
  intro k hk
  have hNonneg : 0 ≤ ∫ ω, |Err k ω| ∂P :=
    integral_nonneg (fun _ => abs_nonneg _)
  have hFinal : η * M < δ := by
    have hId : η * (M + 1) = δ := by
      dsimp [η]
      field_simp
    nlinarith
  have hBound : (∫ ω, |Err k ω| ∂P) < δ :=
    lt_of_le_of_lt
      ((hK k hk).trans
        (mul_le_mul_of_nonneg_left (hEnergy k) (le_of_lt hη)))
      hFinal
  simpa only [Real.dist_eq, sub_zero, abs_of_nonneg hNonneg] using hBound
