-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB109_original_grid_stopped_noise_bounded_by_extended_tube
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T17:24:13.194894+00:00
-- url     : https://prove2.me/submissions/037971a2-cc97-48d2-ba2d-b0a7eaeeec81

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_gbB108_monotone_physical_grid_stop_mask_has_prefix_index
import Theorems.Thm_AvramDividend_Classical_avram_gbB64_original_stopped_discounted_gaussian_mesh_prefix_noise_sup_bound
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
/-- The physical stopped source noise is bounded using one extra mesh interval. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (m : ℕ) (s : ℕ → ℝ≥0) (hs : Monotone s)
    (hs0 : s 0 = 0) (Δ T : ℝ≥0)
    (hstep : ∀ i, s (i + 1) = s i + Δ)
    (hX0 : X.X 0 ω = 0) (q ε : ℝ)
    (hq : 0 ≤ q) (hε : 0 ≤ ε)
    (hTube : ∀ i, s i ≤ T + Δ →
      |X.X (s i) ω - (s i : ℝ) * X.c| ≤ ε) :
    |(Finset.range (m + 1)).sum (fun i =>
      if s i < T then Real.exp (-(q * (s i : ℝ))) *
        (X.X (s (i + 1)) ω - X.X (s i) ω -
          ((s (i + 1) : ℝ) - (s i : ℝ)) * X.c)
      else 0)| ≤ ε := by
  obtain ⟨k, hk, hiff⟩ :=
    avram_gbB108_monotone_physical_grid_stop_mask_has_prefix_index
      s hs T m
  have hsk : s k ≤ T + Δ := by
    cases k with
    | zero =>
        simp [hs0]
    | succ j =>
        have hj : j < m + 1 := by omega
        have hjT : s j < T := (hiff j hj).2 (by omega)
        rw [hstep j]
        simpa only [add_comm] using (add_le_add_right (le_of_lt hjT) Δ)
  have hTubeK (i : ℕ) (hi : i ≤ k) :
      |X.X (s i) ω - (s i : ℝ) * X.c| ≤ ε :=
    hTube i ((hs hi).trans hsk)
  have hmask :
      (Finset.range (m + 1)).sum (fun i =>
        if s i < T then Real.exp (-(q * (s i : ℝ))) *
          (X.X (s (i + 1)) ω - X.X (s i) ω -
            ((s (i + 1) : ℝ) - (s i : ℝ)) * X.c)
        else 0) =
      (Finset.range (m + 1)).sum (fun i =>
        if i < k then Real.exp (-(q * (s i : ℝ))) *
          (X.X (s (i + 1)) ω - X.X (s i) ω -
            ((s (i + 1) : ℝ) - (s i : ℝ)) * X.c)
        else 0) := by
    apply Finset.sum_congr rfl
    intro i hi
    have h : s i < T ↔ i < k :=
      hiff i (Finset.mem_range.mp hi)
    by_cases hlt : s i < T
    · have hik : i < k := h.mp hlt
      simp [hlt, hik]
    · have hik : ¬ i < k := fun hk => hlt (h.mpr hk)
      simp [hlt, hik]
  rw [hmask]
  exact avram_gbB64_original_stopped_discounted_gaussian_mesh_prefix_noise_sup_bound
    X ω m k hk s hs hs0 hX0 q ε hq hε hTubeK
