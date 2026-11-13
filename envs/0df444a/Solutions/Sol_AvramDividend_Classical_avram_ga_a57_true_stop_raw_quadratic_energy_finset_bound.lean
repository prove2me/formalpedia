-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a57_true_stop_raw_quadratic_energy_finset_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T00:33:51.597028+00:00
-- url     : https://prove2.me/submissions/f3dbdd3d-8178-4eb8-93e4-4e89dc5f1562

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical
noncomputable section

/-- A true pre-stop finite-grid Gaussian raw-source quadratic budget from centred energy and deterministic drift. -/
theorem solution {ι : Type*} (S : Finset ι) (z : ι → ℝ)
    (active : ι → Prop) [DecidablePred active] (d : ℝ) :
    Finset.sum S (fun i => if active i then (z i + d)^2 else 0) ≤
      2 * Finset.sum S (fun i => if active i then (z i)^2 else 0) +
        2 * (S.card : ℝ) * d^2 := by
  classical
  have hTerm (i : ι) (hi : i ∈ S) :
      (if active i then (z i + d)^2 else 0) ≤
        2 * (if active i then (z i)^2 else 0) + 2 * d^2 := by
    by_cases h : active i
    · simp only [if_pos h]
      nlinarith [sq_nonneg (z i - d)]
    · simp only [if_neg h, mul_zero, zero_add]
      nlinarith [sq_nonneg d]
  calc
    Finset.sum S (fun i => if active i then (z i + d)^2 else 0) ≤
        Finset.sum S (fun i =>
          2 * (if active i then (z i)^2 else 0) + 2 * d^2) :=
      Finset.sum_le_sum hTerm
    _ = 2 * Finset.sum S (fun i =>
          if active i then (z i)^2 else 0) +
        2 * (S.card : ℝ) * d^2 := by
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum,
        Finset.sum_const_zero, Finset.sum_const, nsmul_eq_mul]
      ring
