-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_b_rate_real_to_ennreal_normalised_moment_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T22:17:34.462581+00:00
-- url     : https://prove2.me/submissions/e69cc9e5-5da0-4a0d-b34d-7f44a53db345

import Mathlib.Data.ENNReal.Inv
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Order.Filter.Tendsto

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter Topology
open scoped ENNReal

theorem solution
    {ι : Type*} (l : Filter ι) (a : ι → ℝ≥0∞) (h : ι → ℝ) (m : ℝ)
    (hfinite : ∀ i, a i ≠ ⊤) (hpos : ∀ i, 0 < h i)
    (hlim : Tendsto (fun i => (a i).toReal / h i) l (nhds m)) :
    Tendsto (fun i => a i / ENNReal.ofReal (h i)) l
      (nhds (ENNReal.ofReal m)) := by
  have hEq :
      (fun i => a i / ENNReal.ofReal (h i)) =
        (fun i => ENNReal.ofReal ((a i).toReal / h i)) := by
    funext i
    rw [ENNReal.ofReal_div_of_pos (hpos i), ENNReal.ofReal_toReal (hfinite i)]
  rw [hEq]
  exact (ENNReal.continuous_ofReal.tendsto m).comp hlim
