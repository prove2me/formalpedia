-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f_assembly_original_grid_mean_limit_of_exact_rate
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T18:55:45.984066+00:00
-- url     : https://prove2.me/submissions/d28e0d92-e582-4339-8d26-f190b40f5e9b

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_negative_band_marked_times_finite
import Theorems.Thm_AvramDividend_Classical_avram_leanlevy_bridge_original_nu_mesh_pair_rate_limit_auto
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical Filter
open scoped NNReal ENNReal BigOperators Topology
noncomputable section
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0) (hT : 0 < T) (n : ℕ) :
    let F : Ω → Finset ℝ≥0 := fun ω =>
      (avram_wave7_06_original_negative_band_marked_times_finite X ω T n).toFinset
    let A : ℕ → Ω → ℝ≥0∞ := fun k ω =>
      (((((F ω ×ˢ F ω).filter (fun p : ℝ≥0 × ℝ≥0 =>
        Nat.ceil ((p.1 : ℝ) * (k : ℝ) / (T : ℝ)) <
          Nat.ceil ((p.2 : ℝ) * (k : ℝ) / (T : ℝ)))).card : ℕ) : ℝ≥0∞))
    (∀ k : ℕ, 0 < k →
      (∫⁻ ω, A k ω ∂P) =
        ENNReal.ofReal
          (((k : ℝ) * ((k : ℝ) - 1) / 2) *
            (((T : ℝ) *
              (X.ν (Iic (-(1 / ((n : ℝ) + 1))))).toReal) ^ 2 /
                (k : ℝ) ^ 2))) →
    Tendsto (fun k => ∫⁻ ω, A k ω ∂P) atTop
      (𝓝 ((((T : ℝ≥0∞) *
        X.ν (Iic (-(1 / ((n : ℝ) + 1))))) ^ 2) / 2)) := by
  intro F A hEq
  have hRate :=
    avram_leanlevy_bridge_original_nu_mesh_pair_rate_limit_auto X T n
  have hEvent : (fun k => ∫⁻ ω, A k ω ∂P) =ᶠ[atTop]
      (fun k : ℕ => ENNReal.ofReal
        (((k : ℝ) * ((k : ℝ) - 1) / 2) *
          (((T : ℝ) *
            (X.ν (Iic (-(1 / ((n : ℝ) + 1))))).toReal) ^ 2 /
              (k : ℝ) ^ 2))) := by
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with k hk
    exact hEq k hk
  exact hRate.congr' hEvent.symm
