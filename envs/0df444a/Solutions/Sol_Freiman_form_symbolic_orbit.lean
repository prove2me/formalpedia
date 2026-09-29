-- Prove2me | solution 1 for Freiman.form_symbolic_orbit
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T20:07:05.17514+00:00
-- url     : https://prove2.me/submissions/b1591d99-1990-470b-a3d5-e2152044d66d

import Definitions.Def_Freiman_reducedForms
import Theorems.Thm_Freiman_cf_convergence
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option maxHeartbeats 800000

open Freiman

theorem solution (a : ℤ → ℕ+) :
    ∃ R : ReducedOrbit, R.digits = a := by
  let f : ℤ → ℝ := fun n => cfValue (fun k : ℕ => a (n + (k : ℤ) + 1))
  let g : ℤ → ℝ := fun n => cfValue (fun k : ℕ => a (n - (k : ℤ) - 1))
  have hf (n : ℤ) : Irrational (f n) ∧ 0 < f n ∧ f n < 1 := by
    exact ⟨(cf_convergence _).2.1, (cf_convergence _).2.2.1,
      (cf_convergence _).2.2.2.1⟩
  have hg (n : ℤ) : Irrational (g n) ∧ 0 < g n ∧ g n < 1 := by
    exact ⟨(cf_convergence _).2.1, (cf_convergence _).2.2.1,
      (cf_convergence _).2.2.2.1⟩
  have hfstep (n : ℤ) : f n = 1 / (((a (n + 1) : ℕ) : ℝ) + f (n + 1)) := by
    dsimp [f]
    rw [(cf_convergence _).2.2.2.2]
    simp only [Nat.cast_zero, add_zero, Nat.cast_add, Nat.cast_one]
    congr 3
    funext k
    congr 1
    omega
  have hgstep (n : ℤ) : g (n + 1) = 1 / (((a n : ℕ) : ℝ) + g n) := by
    dsimp [g]
    rw [(cf_convergence _).2.2.2.2]
    simp only [Nat.cast_zero, sub_zero, add_sub_cancel_right, Nat.cast_add, Nat.cast_one]
    congr 3
    funext k
    congr 1
    omega
  refine ⟨{
    digits := a
    alpha := fun n => ((a n : ℕ) : ℝ) + f n
    beta := g
    alpha_gt := ?_
    beta_pos := fun n => (hg n).2.1
    beta_lt := fun n => (hg n).2.2
    alpha_irr := fun n => (hf n).1.natCast_add _
    beta_irr := fun n => (hg n).1
    digit_floor := ?_
    alpha_step := ?_
    beta_step := hgstep
  }, rfl⟩
  · intro n
    have hd : (1 : ℝ) ≤ (a n : ℕ) := by exact_mod_cast (a n).pos
    linarith [(hf n).2.1]
  · intro n
    symm
    apply Int.floor_eq_iff.mpr
    simp only [Int.cast_natCast]
    constructor <;> linarith [(hf n).2.1, (hf n).2.2]
  · intro n
    have he : ((a n : ℕ) : ℝ) + f n - ((a n : ℕ) : ℝ) = f n := by ring
    rw [he, hfstep n]
    simp
