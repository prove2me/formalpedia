-- Prove2me | solution 2 for AvramDividend.Classical.avram_p4_f_assembly_original_physical_ceil_pair_measurable_all_grid
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T18:37:36.200075+00:00
-- url     : https://prove2.me/submissions/8f953a73-868d-417a-924a-0e31a751e1ee

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_negative_band_marked_times_finite
import Theorems.Thm_AvramDividend_Classical_avram_leanlevy_bridge_uniform_source_grid_endpoints
import Theorems.Thm_AvramDividend_Classical_avram_leanlevy_bridge_original_ceil_grid_intrinsic_pair_sum
import Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_original_grid_pair_sum_measurable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0) (hT : 0 < T) (n : ℕ) :
    let F : Ω → Finset ℝ≥0 := fun ω =>
      (avram_wave7_06_original_negative_band_marked_times_finite X ω T n).toFinset
    ∀ k : ℕ, Measurable (fun ω =>
      (((((F ω ×ˢ F ω).filter (fun p : ℝ≥0 × ℝ≥0 =>
        Nat.ceil ((p.1 : ℝ) * (k : ℝ) / (T : ℝ)) <
          Nat.ceil ((p.2 : ℝ) * (k : ℝ) / (T : ℝ)))).card : ℕ) : ℝ≥0∞))) := by
  classical
  dsimp only
  intro k
  let F : Ω → Finset ℝ≥0 := fun ω =>
    (avram_wave7_06_original_negative_band_marked_times_finite X ω T n).toFinset
  change Measurable (fun ω =>
    (((((F ω ×ˢ F ω).filter (fun p : ℝ≥0 × ℝ≥0 =>
      Nat.ceil ((p.1 : ℝ) * (k : ℝ) / (T : ℝ)) <
        Nat.ceil ((p.2 : ℝ) * (k : ℝ) / (T : ℝ)))).card : ℕ) : ℝ≥0∞)))
  by_cases hk : 0 < k
  · let s : Fin k → ℝ≥0 := fun i => ((i.val : ℝ≥0) * T) / (k : ℝ≥0)
    let t : Fin k → ℝ≥0 := fun i => (((i.val + 1 : ℕ) : ℝ≥0) * T) / (k : ℝ≥0)
    obtain ⟨hst, htT, hs, ht⟩ :=
      avram_leanlevy_bridge_uniform_source_grid_endpoints T k hk
    let B : Set ℝ := Iic (-(1 / ((n : ℝ) + 1)))
    let N : ℝ≥0 → ℝ≥0 → Ω → ℝ≥0∞ := fun a b ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc a b ×ˢ B)
    have hMeas : Measurable (fun ω =>
        ∑ i : Fin k, N 0 (s i) ω * N (s i) (t i) ω) := by
      simpa only [N, B] using
        (avram_p2_e_compensator_original_grid_pair_sum_measurable X k s t n)
    have hPoint (ω : Ω) :
        (((((F ω ×ˢ F ω).filter (fun p : ℝ≥0 × ℝ≥0 =>
          Nat.ceil ((p.1 : ℝ) * (k : ℝ) / (T : ℝ)) <
            Nat.ceil ((p.2 : ℝ) * (k : ℝ) / (T : ℝ)))).card : ℕ) : ℝ≥0∞)) =
        ∑ i : Fin k, N 0 (s i) ω * N (s i) (t i) ω := by
      simpa only [N, B, s, t] using
        (avram_leanlevy_bridge_original_ceil_grid_intrinsic_pair_sum
          X T hT n k hk s t hst htT hs ht ω)
    rw [show (fun ω : Ω =>
      (((((F ω ×ˢ F ω).filter (fun p : ℝ≥0 × ℝ≥0 =>
        Nat.ceil ((p.1 : ℝ) * (k : ℝ) / (T : ℝ)) <
          Nat.ceil ((p.2 : ℝ) * (k : ℝ) / (T : ℝ)))).card : ℕ) : ℝ≥0∞))) =
      (fun ω => ∑ i : Fin k, N 0 (s i) ω * N (s i) (t i) ω) from funext hPoint]
    exact hMeas
  · have hk0 : k = 0 := Nat.eq_zero_of_not_pos hk
    subst k
    simpa [F] using (measurable_const : Measurable (fun _ : Ω => (0 : ℝ≥0∞)))
