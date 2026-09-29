-- Prove2me | solution 1 for BlockCycleRotation.continuousAt_fCost
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-05T12:01:37.863843+00:00
-- url     : https://prove2.me/submissions/fd88fda5-1209-4c75-ae56-271c5a8c2d90

import Definitions.Def_BlockCycleRotation_Algorithm
import Definitions.Def_BlockCycleRotation_Continuant
import Definitions.Def_BlockCycleRotation_Euclid
import Definitions.Def_BlockCycleRotation_ExpSum
import Definitions.Def_BlockCycleRotation_Theorem10
import Theorems.Thm_BlockCycleRotation_continuousAt_psi
import Mathlib

open Finset Real Filter Topology MeasureTheory BoxIntegral
open scoped ENNReal

namespace BlockCycleRotation

@[simp]
theorem remSum_zero (n : ℕ) : remSum n 0 = 0 := by
  rw [remSum]; simp

@[simp]
theorem norm_e (θ : ℝ) : ‖e θ‖ = 1 := Complex.norm_exp_ofReal_mul_I θ

@[simp]
theorem norm_e_pow (θ : ℝ) (n : ℕ) : ‖e θ ^ n‖ = 1 := by
  rw [norm_pow, norm_e, one_pow]

@[simp]
theorem cost_zero (n : ℕ) : cost n 0 = 0 := by
  rw [cost]; simp

@[simp]
theorem finalSeg_zero (n : ℕ) : finalSeg n 0 = n := by
  rw [finalSeg]; simp

@[simp]
theorem e_zero : e 0 = 1 := by simp [e]

@[simp] theorem K_nil : K [] = 1 := rfl

@[simp] theorem K_singleton (c : ℕ) : K [c] = c := rfl

@[simp] theorem cf_zero (a : ℕ) : cf a 0 = [] := by rw [cf]; simp

end BlockCycleRotation

open BlockCycleRotation in
/-- **`f` is continuous at every irrational point of `(0,1)`.** -/
theorem solution {x : ℝ} (hirr : Irrational x) (hx0 : 0 < x) (hx : x < 1) :
    ContinuousAt fCost x:= by
  have hne : x ≠ 1 / 2 := by
    intro h
    exact Irrational.ne_rat hirr (1 / 2) (by rw [h]; norm_num)
  have hmin : min x (1 - x) < 1 / 2 := by
    rcases lt_or_gt_of_ne hne with h | h
    · rw [min_eq_left (by linarith)]; exact h
    · rw [min_eq_right (by linarith)]; linarith
  have hmin0 : 0 < min x (1 - x) := by
    rw [lt_min_iff]
    exact ⟨hx0, by linarith⟩
  have hmirr : Irrational (min x (1 - x)) := by
    rcases le_total x (1 - x) with h | h
    · rw [min_eq_left h]; exact hirr
    · rw [min_eq_right h]
      have h1 : Irrational (x - 1) := by
        have := Irrational.sub_intCast hirr 1
        simpa using this
      have h2 : (1 : ℝ) - x = -(x - 1) := by ring
      rw [h2]
      exact Irrational.neg h1
  have hc : ContinuousAt (fun y : ℝ => min y (1 - y)) x :=
    continuousAt_id.min (continuousAt_const.sub continuousAt_id)
  have hcomp : ContinuousAt (fun y : ℝ => psi (min y (1 - y))) x :=
    ContinuousAt.comp (g := psi) (continuousAt_psi hmirr hmin0 hmin) hc
  unfold fCost
  exact continuousAt_const.add hcomp
