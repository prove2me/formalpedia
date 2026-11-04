-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_b_rate_eventual_all_power_tail_bounds_tendsto_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T19:59:04.899532+00:00
-- url     : https://prove2.me/submissions/a032b852-d32c-410b-ac58-ddc12b1c7b22

import Mathlib
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Order.Basic
import Mathlib.Topology.Algebra.Order.Field

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter Topology

theorem solution
    {ι : Type*} (l : Filter ι) (f : ι → ℝ)
    (R C : ℝ) (hR : 1 < R)
    (hf0 : ∀ᶠ i in l, 0 ≤ f i)
    (hbound : ∀ k : ℕ, ∀ᶠ i in l, R ^ k * f i ≤ C) :
    Tendsto f l (nhds 0) := by
  have hRpos : 0 < R := by linarith
  have hlim : Tendsto (fun k : ℕ => C / R ^ k) atTop (nhds 0) := by
    have hpow : Tendsto (fun k : ℕ => R ^ k) atTop atTop :=
      tendsto_pow_atTop_atTop_of_one_lt hR
    simpa using (tendsto_const_nhds.div_atTop hpow)
  refine tendsto_order.2 ⟨?_, ?_⟩
  · intro a ha
    filter_upwards [hf0] with i hi
    linarith
  · intro a ha
    have hk : ∀ᶠ k : ℕ in atTop, C / R ^ k < a :=
      (tendsto_order.1 hlim).2 a ha
    obtain ⟨k, hk'⟩ := hk.exists
    filter_upwards [hbound k] with i hi
    have hle : f i ≤ C / R ^ k :=
      (le_div_iff₀ (pow_pos hRpos k)).2 (by
        simpa [mul_comm] using hi)
    linarith
