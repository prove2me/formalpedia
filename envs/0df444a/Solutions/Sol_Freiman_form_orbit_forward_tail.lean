-- Prove2me | solution 1 for Freiman.form_orbit_forward_tail
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T20:07:57.106842+00:00
-- url     : https://prove2.me/submissions/a61ed45a-fa1b-4e2e-a297-fbb3bac01776

import Definitions.Def_Freiman_reducedForms
import Theorems.Thm_Freiman_cf_convergence
import Theorems.Thm_Freiman_cfValue_prefix
import Theorems.Thm_Freiman_prefixEval_cylinder_bound
import Theorems.Thm_Freiman_cylinder_bound_tendsto
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option maxHeartbeats 800000

open Freiman Filter Topology

namespace FreimanForwardTailProof

lemma reconstruct (u : ℕ → ℝ) (b : ℕ → ℕ+)
    (hu : ∀ k, u k = 1 / (((b k : ℕ) : ℝ) + u (k + 1)))
    (m k : ℕ) :
    u k = prefixEval ((List.range m).map (fun i => b (k + i))) (u (k + m)) := by
  induction m generalizing k with
  | zero => simp [prefixEval]
  | succ m ih =>
    rw [List.range_succ_eq_map, List.map_cons, List.map_map, prefixEval]
    simp only [Nat.add_zero, Function.comp_def]
    rw [hu k, ih (k + 1)]
    simp only [Nat.succ_eq_add_one, Nat.add_left_comm, Nat.add_comm]

lemma identify (u : ℕ → ℝ) (b : ℕ → ℕ+)
    (hu : ∀ k, u k = 1 / (((b k : ℕ) : ℝ) + u (k + 1)))
    (hum : ∀ k, u k ∈ Set.Icc (0 : ℝ) 1) : u 0 = cfValue b := by
  have hp (m : ℕ) : u 0 = prefixEval ((List.range m).map b) (u m) := by
    simpa using reconstruct u b hu m 0
  have hb (m : ℕ) : |u 0 - cfValue b| ≤ 2 / ((Nat.fib (m + 1) : ℝ) ^ 2) := by
    have hm := cf_convergence (fun k => b (m + k))
    have hc := prefixEval_cylinder_bound ((List.range m).map b) (u m)
      (cfValue (fun k => b (m + k))) (hum m)
      ⟨hm.2.2.1.le, hm.2.2.2.1.le⟩
    rw [← hp m, ← cfValue_prefix b m] at hc
    simp only [List.length_map, List.length_range] at hc
    exact hc.trans (div_le_div_of_nonneg_right (by norm_num) (sq_nonneg _))
  exact sub_eq_zero.mp (abs_nonpos_iff.mp (ge_of_tendsto' cylinder_bound_tendsto hb))

end FreimanForwardTailProof

open FreimanForwardTailProof in
theorem solution (R : ReducedOrbit) (n : ℤ) :
    R.alpha n = ((R.digits n : ℕ) : ℝ) +
      cfValue (fun k : ℕ => R.digits (n + (k : ℤ) + 1)) := by
  have he (i : ℤ) :
      R.alpha i = ((R.digits i : ℕ) : ℝ) + 1 / R.alpha (i + 1) := by
    rw [R.alpha_step i]
    simp only [one_div, inv_inv]
    ring
  let b : ℕ → ℕ+ := fun k => R.digits (n + (k : ℤ) + 1)
  let u : ℕ → ℝ := fun k => 1 / R.alpha (n + (k : ℤ) + 1)
  have hu : ∀ k, u k = 1 / (((b k : ℕ) : ℝ) + u (k + 1)) := by
    intro k
    simpa [u, b, Nat.cast_add, Nat.cast_one, add_assoc] using
      congrArg (fun z : ℝ => 1 / z) (he (n + (k : ℤ) + 1))
  have hum (k : ℕ) : u k ∈ Set.Icc (0 : ℝ) 1 := by
    have ha := R.alpha_gt (n + (k : ℤ) + 1)
    constructor
    · exact div_nonneg (by norm_num) (by linarith)
    · exact (div_le_one (by linarith)).2 ha.le
  have hval := identify u b hu hum
  have hzero : 1 / R.alpha (n + 1) = cfValue b := by simpa [u] using hval
  simpa [b, hzero] using he n
