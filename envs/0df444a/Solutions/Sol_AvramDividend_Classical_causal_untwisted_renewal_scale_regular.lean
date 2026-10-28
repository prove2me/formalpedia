-- Prove2me | solution 1 for AvramDividend.Classical.causal_untwisted_renewal_scale_regular
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T08:28:27.715575+00:00
-- url     : https://prove2.me/submissions/57d1b0ba-cd79-451f-b68c-aa67bbb1b02e

import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic.Ring
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- The untwisted renewal sum is a supported, nonnegative, continuous, monotone scale candidate. -/
theorem solution
    (F U : ℕ → ℝ → ℝ) (θ q : ℝ) (hq : 0 < q)
    (hFzero : ∀ n : ℕ, ∀ x : ℝ, x ≤ 0 → F n x = 0)
    (hrel : ∀ n : ℕ, ∀ x : ℝ,
      F n x = Real.exp (-(θ * x)) * U n x)
    (hUmono : ∀ n : ℕ, Monotone (U n))
    (hUcont : ContinuousOn (fun x : ℝ => ∑' n : ℕ, U n x) (Ici 0))
    (hUmonosum : MonotoneOn (fun x : ℝ => ∑' n : ℕ, U n x) (Ici 0)) :
    ∃ W : ℝ → ℝ,
      (∀ x : ℝ, W x =
        (Real.exp (θ * x) / q) * (∑' n : ℕ, F n x)) ∧
      (∀ x : ℝ, x < 0 → W x = 0) ∧
      (∀ x : ℝ, 0 ≤ x → 0 ≤ W x) ∧
      ContinuousOn W (Ici (0 : ℝ)) ∧
      MonotoneOn W (Ici (0 : ℝ)) := by
  let W : ℝ → ℝ := fun x => (1 / q) * (∑' n : ℕ, U n x)
  have hUzero (n : ℕ) (x : ℝ) (hx : x ≤ 0) : U n x = 0 := by
    have hh : Real.exp (-(θ * x)) * U n x = 0 := by
      rw [← hrel n x]
      exact hFzero n x hx
    exact (mul_eq_zero.mp hh).resolve_left (Real.exp_ne_zero _)
  have hUeqF (n : ℕ) (x : ℝ) :
      U n x = Real.exp (θ * x) * F n x := by
    calc
      U n x = (Real.exp (θ * x) * Real.exp (-(θ * x))) * U n x := by
        rw [← Real.exp_add]
        simp
      _ = Real.exp (θ * x) * F n x := by rw [hrel n x]; ring
  have hsumrel (x : ℝ) :
      (∑' n : ℕ, U n x) =
        Real.exp (θ * x) * (∑' n : ℕ, F n x) := by
    simp_rw [hUeqF]
    rw [tsum_mul_left]
  have hWform (x : ℝ) :
      W x = (Real.exp (θ * x) / q) * (∑' n : ℕ, F n x) := by
    dsimp [W]
    rw [hsumrel]
    ring
  have hWzero (x : ℝ) (hx : x < 0) : W x = 0 := by
    have h (n : ℕ) : U n x = 0 :=
      hUzero n x (le_of_lt hx)
    simp [W, h]
  have hWpos (x : ℝ) (hx : 0 ≤ x) : 0 ≤ W x := by
    have hun (n : ℕ) : 0 ≤ U n x := by
      have hm := hUmono n hx
      simpa [hUzero n 0 le_rfl] using hm
    exact mul_nonneg (le_of_lt (one_div_pos.mpr hq))
      (tsum_nonneg hun)
  have hWcont : ContinuousOn W (Ici (0 : ℝ)) := by
    exact continuousOn_const.mul hUcont
  have hWmono : MonotoneOn W (Ici (0 : ℝ)) := by
    intro x hx y hy hxy
    exact mul_le_mul_of_nonneg_left
      (hUmonosum hx hy hxy) (le_of_lt (one_div_pos.mpr hq))
  exact ⟨W, hWform, hWzero, hWpos, hWcont, hWmono⟩
