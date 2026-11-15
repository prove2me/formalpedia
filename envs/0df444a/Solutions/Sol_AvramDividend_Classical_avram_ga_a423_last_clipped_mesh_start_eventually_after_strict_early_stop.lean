-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a423_last_clipped_mesh_start_eventually_after_strict_early_stop
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T18:49:52.76841+00:00
-- url     : https://prove2.me/submissions/0f68f32d-cdc0-4229-a453-5ca52f9fb47b

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_uniform_nnreal_width_tendsto_zero
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter Topology AvramDividend.Classical
open scoped NNReal
noncomputable section

theorem solution
    (T ρ : ℝ≥0) (hρ : ρ < T) :
    ∃ k : ℕ, ∀ m : ℕ, k ≤ m →
      let Δ : ℝ≥0 := T / ((m : ℝ≥0) + 1)
      ρ ≤ (m : ℝ≥0) * Δ := by
  let Δ : ℕ → ℝ≥0 := fun m => T / ((m : ℝ≥0) + 1)
  have hw : Tendsto (fun m : ℕ => (Δ m : ℝ))
      atTop (𝓝 (0 : ℝ)) := by
    exact NNReal.tendsto_coe.mpr
      (avram_p2_a_zero_rate_uniform_nnreal_width_tendsto_zero T)
  have hg : (0 : ℝ) < (T : ℝ) - (ρ : ℝ) := by
    exact sub_pos.mpr (by exact_mod_cast hρ)
  have hev : ∀ᶠ m : ℕ in atTop,
      (Δ m : ℝ) < (T : ℝ) - (ρ : ℝ) :=
    hw.eventually (isOpen_Iio.mem_nhds hg)
  obtain ⟨k,hk⟩ := Filter.eventually_atTop.1 hev
  refine ⟨k, ?_⟩
  intro m hm
  have hr := hk m hm
  have hEq : ((m : ℝ≥0) + 1) * Δ m = T := by
    dsimp [Δ]
    field_simp
  have hCo : ((m : ℝ) + 1) * (Δ m : ℝ) = (T : ℝ) := by
    exact_mod_cast hEq
  have hTarget : (ρ : ℝ) ≤ (m : ℝ) * (Δ m : ℝ) := by
    nlinarith
  have hNN : ρ ≤ (m : ℝ≥0) * Δ m := by
    apply (NNReal.coe_le_coe).mp
    simpa only [NNReal.coe_mul, NNReal.coe_natCast] using hTarget
  simpa only [Δ] using hNN
