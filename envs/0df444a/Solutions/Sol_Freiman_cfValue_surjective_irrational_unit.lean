-- Prove2me | solution 1 for Freiman.cfValue_surjective_irrational_unit
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T19:58:19.390617+00:00
-- url     : https://prove2.me/submissions/89a82b5d-55de-41ea-b4c1-3bd0cac94394

import Theorems.Thm_Freiman_cf_convergence
import Theorems.Thm_Freiman_cfValue_prefix
import Theorems.Thm_Freiman_prefixEval_cylinder_bound
import Theorems.Thm_Freiman_cylinder_bound_tendsto
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Logic.Function.Iterate
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option maxHeartbeats 800000

open Freiman Filter Topology

namespace FreimanSurjectiveProof

/-- The Gauss map acts on irrational points of the open unit interval. -/
abbrev UnitIrrational := {x : ℝ // Irrational x ∧ 0 < x ∧ x < 1}

noncomputable def next (z : UnitIrrational) : UnitIrrational := by
  let r : ℝ := (z : ℝ)⁻¹ - (⌊(z : ℝ)⁻¹⌋₊ : ℝ)
  have hi : Irrational r := z.property.1.inv.sub_natCast _
  have hnonneg : 0 ≤ r :=
    sub_nonneg.mpr (Nat.floor_le (inv_nonneg.mpr z.property.2.1.le))
  refine ⟨r, hi, lt_of_le_of_ne hnonneg (Ne.symm hi.ne_zero), ?_⟩
  have hf := Nat.lt_floor_add_one ((z : ℝ)⁻¹)
  dsimp [r]
  linarith

noncomputable def digit (z : UnitIrrational) : ℕ+ :=
  ⟨⌊(z : ℝ)⁻¹⌋₊, Nat.floor_pos.mpr (by
    rw [← one_div]
    apply (le_div_iff₀ z.property.2.1).2
    simpa using z.property.2.2.le)⟩

lemma next_identity (z : UnitIrrational) :
    (z : ℝ) = 1 / (((digit z : ℕ) : ℝ) + (next z : ℝ)) := by
  change (z : ℝ) = 1 / ((⌊(z : ℝ)⁻¹⌋₊ : ℝ) +
    ((z : ℝ)⁻¹ - (⌊(z : ℝ)⁻¹⌋₊ : ℝ)))
  have he : (⌊(z : ℝ)⁻¹⌋₊ : ℝ) +
      ((z : ℝ)⁻¹ - (⌊(z : ℝ)⁻¹⌋₊ : ℝ)) = (z : ℝ)⁻¹ := by ring
  rw [he, one_div, inv_inv]

/-- Iterating the complete-quotient identity gives every finite prefix. -/
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

end FreimanSurjectiveProof

open FreimanSurjectiveProof in
theorem solution (x : ℝ) (hx : Irrational x) (h0 : 0 < x) (h1 : x < 1) :
    ∃ b : ℕ → ℕ+, cfValue b = x := by
  let z : UnitIrrational := ⟨x, hx, h0, h1⟩
  let states : ℕ → UnitIrrational := fun n => next^[n] z
  let b : ℕ → ℕ+ := fun n => digit (states n)
  let u : ℕ → ℝ := fun n => (states n : ℝ)
  have hu : ∀ k, u k = 1 / (((b k : ℕ) : ℝ) + u (k + 1)) := by
    intro k
    simpa only [u, b, states, Function.iterate_succ_apply'] using
      next_identity (states k)
  have hp (m : ℕ) :
      x = prefixEval ((List.range m).map b) (u m) := by
    simpa [u, states, z] using reconstruct u b hu m 0
  have hbound (m : ℕ) :
      |x - cfValue b| ≤ 2 / ((Nat.fib (m + 1) : ℝ) ^ 2) := by
    have hm := cf_convergence (fun k => b (m + k))
    have hc := prefixEval_cylinder_bound ((List.range m).map b) (u m)
      (cfValue (fun k => b (m + k)))
      ⟨(states m).property.2.1.le, (states m).property.2.2.le⟩
      ⟨hm.2.2.1.le, hm.2.2.2.1.le⟩
    rw [← hp m, ← cfValue_prefix b m] at hc
    simp only [List.length_map, List.length_range] at hc
    exact hc.trans (div_le_div_of_nonneg_right (by norm_num) (sq_nonneg _))
  have hz : |x - cfValue b| ≤ 0 := ge_of_tendsto' cylinder_bound_tendsto hbound
  exact ⟨b, (sub_eq_zero.mp (abs_nonpos_iff.mp hz)).symm⟩
