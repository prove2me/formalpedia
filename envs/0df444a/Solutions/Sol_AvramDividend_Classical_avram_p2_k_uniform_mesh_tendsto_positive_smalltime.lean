-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_k_uniform_mesh_tendsto_positive_smalltime
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T20:17:44.169578+00:00
-- url     : https://prove2.me/submissions/3b2a8e45-a0fd-409d-8712-a111d56b4daa

import Mathlib.Data.Real.Basic
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Order.Filter.AtTopBot.Archimedean
import Mathlib.Order.Filter.AtTopBot.Group
import Mathlib.Topology.NhdsWithin

open Filter Topology Set

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

/-- The fixed-horizon uniform mesh approaches zero from positive times,
so any original-source small-time rate can be evaluated along this mesh. -/
theorem solution
    (T : ℝ) (hT : 0 < T) :
    Tendsto (fun n : ℕ => T / ((n : ℝ) + 1)) atTop
      (nhdsWithin (0 : ℝ) (Ioi 0)) := by
  have hden : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
    Filter.tendsto_atTop_add_const_right atTop (1 : ℝ)
      (tendsto_natCast_atTop_atTop :
        Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop)
  have hinv :
      Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹) atTop
        (nhds (0 : ℝ)) := tendsto_inv_atTop_zero.comp hden
  have hzero :
      Tendsto (fun n : ℕ => T / ((n : ℝ) + 1)) atTop
        (nhds (0 : ℝ)) := by
    simpa only [div_eq_mul_inv, mul_zero] using
      (tendsto_const_nhds.mul hinv :
        Tendsto (fun n : ℕ => T * ((n : ℝ) + 1)⁻¹)
          atTop (nhds (T * (0 : ℝ))))
  apply (tendsto_nhdsWithin_iff).2
  refine ⟨hzero, Filter.Eventually.of_forall ?_⟩
  intro n
  exact div_pos hT (add_pos_of_nonneg_of_pos (Nat.cast_nonneg n) zero_lt_one)
