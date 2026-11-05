-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f_assembly_original_ceil_pairs_eq_physical_grid
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T18:33:12.994086+00:00
-- url     : https://prove2.me/submissions/f53bb639-8e80-4367-b1f4-1e658a917a27

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_leanlevy_bridge_uniform_source_grid_endpoints
import Theorems.Thm_AvramDividend_Classical_avram_leanlevy_bridge_original_ceil_grid_intrinsic_pair_sum

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (T : ℝ≥0) (hT : 0 < T) (n k : ℕ) (hk : 0 < k) :
    let F : Finset ℝ≥0 :=
      (avram_wave7_06_original_negative_band_marked_times_finite X ω T n).toFinset
    let s : Fin k → ℝ≥0 := fun i => ((i.val : ℝ≥0) * T) / (k : ℝ≥0)
    let t : Fin k → ℝ≥0 := fun i => (((i.val + 1 : ℕ) : ℝ≥0) * T) / (k : ℝ≥0)
    let Npast : Fin k → ℝ≥0∞ := fun i =>
      ((Measure.count.restrict {u : ℝ≥0 | 0 < u ∧
        X.X u ω - Function.leftLim (fun y : ℝ≥0 => X.X y ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun y : ℝ≥0 => X.X y ω) u)))
        (Ioc 0 (s i) ×ˢ Iic (-(1 / ((n : ℝ) + 1))))
    let Nfuture : Fin k → ℝ≥0∞ := fun i =>
      ((Measure.count.restrict {u : ℝ≥0 | 0 < u ∧
        X.X u ω - Function.leftLim (fun y : ℝ≥0 => X.X y ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun y : ℝ≥0 => X.X y ω) u)))
        (Ioc (s i) (t i) ×ˢ Iic (-(1 / ((n : ℝ) + 1))))
    (((F ×ˢ F).filter (fun p : ℝ≥0 × ℝ≥0 =>
      Nat.ceil ((p.1 : ℝ) * (k : ℝ) / (T : ℝ)) <
        Nat.ceil ((p.2 : ℝ) * (k : ℝ) / (T : ℝ)))).card : ℝ≥0∞) =
      ∑ i : Fin k, Npast i * Nfuture i := by
  dsimp only
  obtain ⟨hst, htT, hs, ht⟩ :=
    avram_leanlevy_bridge_uniform_source_grid_endpoints T k hk
  have hphysical :=
    avram_leanlevy_bridge_original_ceil_grid_intrinsic_pair_sum
      X T hT n k hk
      (fun i => ((i.val : ℝ≥0) * T) / (k : ℝ≥0))
      (fun i => (((i.val + 1 : ℕ) : ℝ≥0) * T) / (k : ℝ≥0))
      hst htT hs ht ω
  exact hphysical
