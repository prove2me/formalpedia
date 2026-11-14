-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb50_original_uniform_final_strip_BV_source_equals_physical_drift_ae
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T12:57:00.517907+00:00
-- url     : https://prove2.me/submissions/301f2c5b-536a-4412-82bb-8b875fcec847

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_bvb45_original_uniform_grid_eventually_excludes_all_final_source_negative_marks
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_bv_actual_no_jump_interval_is_drift_only
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid4_original_uniform_strict_mesh_cofinal_at_horizon
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- On the actual original finite negative-jump BV source, every sufficiently
fine final strict physical grid cell evolves exactly by the BV drift. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (T : ℝ) (hT : 0 < T)
    (u : ℕ → ℕ → ℝ≥0)
    (hgrid : ∀ n, (u n (n + 1) : ℝ) =
      T - T / ((n : ℝ) + 2))
    (huniform : ∀ n i, (u n i : ℝ) =
      T * (i : ℝ) / ((n : ℝ) + 2)) :
    let S : ℝ≥0 := ⟨T,le_of_lt hT⟩
    ∀ᵐ ω ∂P, ∀ᶠ n in (atTop : Filter ℕ),
      X.X S ω - X.X (u n (n + 1)) ω =
        ((S : ℝ) - (u n (n + 1) : ℝ)) * X.drift := by
  intro S
  have hS : 0 < S := by
    exact_mod_cast hT
  have hFinitePath :=
    avram_wave4_04a_bv_actual_no_jump_interval_is_drift_only
      X hBV hFinite S hS
  have hNoTerminal :=
    avram_bvb45_original_uniform_grid_eventually_excludes_all_final_source_negative_marks
      X hBV hFinite T hT u huniform
  filter_upwards [hFinitePath,hNoTerminal] with ω hDrift hNo
  filter_upwards [hNo] with n hn
  have hEnd : (u n (n + 1) : ℝ) < T := by
    rw [hgrid n]
    exact ((avram_p3_grid4_original_uniform_strict_mesh_cofinal_at_horizon T hT).1 n).2
  have huS : u n (n + 1) ≤ S := by
    exact_mod_cast hEnd.le
  have hNoJump : ∀ t : ℝ≥0, t ∈ Ioc (u n (n + 1)) S →
      X.X t ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) t = 0 := by
    intro t ht
    by_contra hne
    have htpos : 0 < t := lt_of_le_of_lt (show (0 : ℝ≥0) ≤ u n (n + 1) from bot_le) ht.1
    exact hn t htpos (by exact_mod_cast ht.1)
      (by exact_mod_cast ht.2) hne
  have h := hDrift (u n (n + 1)) S huS le_rfl hNoJump
  have hDiff : (S : ℝ) * X.drift - X.X S ω =
      (u n (n + 1) : ℝ) * X.drift - X.X (u n (n + 1)) ω := h
  linarith
