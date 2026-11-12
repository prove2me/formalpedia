-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB103_uniform_mesh_left_approximation_squeeze
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T22:35:15.87019+00:00
-- url     : https://prove2.me/submissions/ba8cbca1-eac0-4c20-9a13-a24597412082

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter Topology
noncomputable section

theorem solution
    (n : ℕ) (hn : 0 < n) (t : ℝ)
    (s : ℕ → ℝ)
    (hLeft : ∀ m, s m ≤ t)
    (hGap : ∀ m, t - s m ≤ (n : ℝ) / ((m : ℝ) + 1)) :
    Tendsto s atTop (𝓝 t) := by
  have hInv :
      Tendsto (fun m : ℕ => (n : ℝ) / ((m : ℝ) + 1))
        atTop (𝓝 (0 : ℝ)) := by
    simpa [div_eq_mul_inv] using
      ((tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul
        (n : ℝ))
  have hLo :
      Tendsto (fun m : ℕ => t - (n : ℝ) / ((m : ℝ) + 1))
        atTop (𝓝 t) := by
    simpa using (tendsto_const_nhds.sub hInv)
  have hHi :
      Tendsto (fun _ : ℕ => t) atTop (𝓝 t) :=
    tendsto_const_nhds
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le hLo hHi
  · intro m
    linarith [hGap m]
  · intro m
    exact hLeft m
