-- Prove2me | solution 1 for BlockCycleRotation.continuousAt_psi
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-05T12:01:37.795876+00:00
-- url     : https://prove2.me/submissions/2bc2861a-1422-4e04-b9ad-e4472df27a2e

import Definitions.Def_BlockCycleRotation_Algorithm
import Definitions.Def_BlockCycleRotation_Continuant
import Definitions.Def_BlockCycleRotation_Euclid
import Definitions.Def_BlockCycleRotation_ExpSum
import Definitions.Def_BlockCycleRotation_Theorem10
import Theorems.Thm_BlockCycleRotation_irrational_Inn
import Theorems.Thm_BlockCycleRotation_psi_sub_partial_le
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

theorem irrational_ne_zero {x : ℝ} (h : Irrational x) : x ≠ 0 := by
  intro hx
  exact Irrational.ne_int h 0 (by simp [hx])

theorem irrational_one_div {x : ℝ} (h : Irrational x) : Irrational (1 / x) := by
  rw [one_div]
  exact Irrational.inv h

theorem iterate_Inn_irrational {x : ℝ} (h : Irrational x) (m : ℕ) :
    Irrational (Inn^[m] x) := by
  induction m with
  | zero => exact h
  | succ j ih => rw [Function.iterate_succ_apply']; exact irrational_Inn ih

theorem continuousAt_Inn {x : ℝ} (h : Irrational x) : ContinuousAt Inn x := by
  have hx0 : x ≠ 0 := irrational_ne_zero h
  have hne : 1 / x ≠ ((⌊1 / x⌋ : ℤ) : ℝ) := Irrational.ne_int (irrational_one_div h) _
  have hcinv : ContinuousAt (fun y : ℝ => 1 / y) x := continuousAt_const.div continuousAt_id hx0
  have hcomp : ContinuousAt (fun y : ℝ => Int.fract (1 / y)) x :=
    (continuousAt_fract hne).comp hcinv
  have hgnn : (0 : ℝ) ≤ Int.fract (1 / x) := Int.fract_nonneg _
  have hden : (1 : ℝ) + Int.fract (1 / x) ≠ 0 := by positivity
  have hform : ContinuousAt
      (fun y : ℝ => Int.fract (1 / y) / (1 + Int.fract (1 / y))) x :=
    hcomp.div (continuousAt_const.add hcomp) hden
  refine hform.congr ?_
  filter_upwards [isOpen_ne.mem_nhds hx0] with y hy
  unfold Inn
  rw [if_neg hy]

theorem continuousAt_Outt {x : ℝ} (h : Irrational x) : ContinuousAt Outt x := by
  have hx0 : x ≠ 0 := irrational_ne_zero h
  have hne : 1 / x ≠ ((⌊1 / x⌋ : ℤ) : ℝ) := Irrational.ne_int (irrational_one_div h) _
  have hcinv : ContinuousAt (fun y : ℝ => 1 / y) x := continuousAt_const.div continuousAt_id hx0
  have hcomp : ContinuousAt (fun y : ℝ => Int.fract (1 / y)) x :=
    (continuousAt_fract hne).comp hcinv
  have hform : ContinuousAt (fun y : ℝ => y * (1 + Int.fract (1 / y))) x :=
    continuousAt_id.mul (continuousAt_const.add hcomp)
  refine hform.congr ?_
  filter_upwards [isOpen_ne.mem_nhds hx0] with y hy
  unfold Outt
  rw [if_neg hy]

theorem continuousAt_iterate_Inn {x : ℝ} (h : Irrational x) (m : ℕ) :
    ContinuousAt (fun y => Inn^[m] y) x := by
  induction m with
  | zero => exact continuousAt_id
  | succ j ih =>
    have hj : ContinuousAt Inn (Inn^[j] x) := continuousAt_Inn (iterate_Inn_irrational h j)
    have heq : (fun y => Inn^[j + 1] y) = (fun y => Inn (Inn^[j] y)) := by
      funext y
      rw [Function.iterate_succ_apply']
    rw [heq]
    exact hj.comp ih

theorem continuousAt_prod_Outt {x : ℝ} (h : Irrational x) (i : ℕ) :
    ContinuousAt (fun y => ∏ m ∈ Finset.range i, Outt (Inn^[m] y)) x := by
  induction i with
  | zero => simpa using continuousAt_const
  | succ j ih =>
    have heq : (fun y => ∏ m ∈ Finset.range (j + 1), Outt (Inn^[m] y))
        = (fun y => (∏ m ∈ Finset.range j, Outt (Inn^[m] y)) * Outt (Inn^[j] y)) := by
      funext y
      rw [Finset.prod_range_succ]
    rw [heq]
    exact ih.mul ((continuousAt_Outt (iterate_Inn_irrational h j)).comp
      (continuousAt_iterate_Inn h j))

theorem continuousAt_psiTerm {x : ℝ} (h : Irrational x) (i : ℕ) :
    ContinuousAt (fun y => psiTerm y i) x := by
  unfold psiTerm
  exact (continuousAt_const.mul (continuousAt_prod_Outt h i)).mul (continuousAt_iterate_Inn h i)

theorem continuousAt_psiPartial {x : ℝ} (h : Irrational x) (N : ℕ) :
    ContinuousAt (psiPartial N) x := by
  induction N with
  | zero =>
    have h0 : psiPartial 0 = fun _ : ℝ => (0 : ℝ) := by
      funext y
      simp [psiPartial]
    rw [h0]
    exact continuousAt_const
  | succ j ih =>
    have heq : psiPartial (j + 1) = fun y => psiPartial j y + psiTerm y j := by
      funext y
      rw [psiPartial, psiPartial, Finset.sum_range_succ]
    rw [heq]
    exact ih.add (continuousAt_psiTerm h j)

end BlockCycleRotation

open BlockCycleRotation in
/-- **Theorem 8.**  `ψ` is continuous at every irrational point of `(0,1/2)`. -/
theorem solution {x : ℝ} (hirr : Irrational x) (hx0 : 0 < x) (hx : x < 1 / 2) :
    ContinuousAt psi x:= by
  rw [Metric.continuousAt_iff]
  intro ε hε
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one (by positivity : (0 : ℝ) < ε / 9)
    (by norm_num : (2 / 3 : ℝ) < 1)
  have hcont := continuousAt_psiPartial hirr N
  rw [Metric.continuousAt_iff] at hcont
  obtain ⟨δ₁, hδ₁, hδ₁'⟩ := hcont (ε / 3) (by linarith)
  refine ⟨min δ₁ (min x (1 / 2 - x)), by positivity, fun y hy => ?_⟩
  have hy1 : dist y x < δ₁ := lt_of_lt_of_le hy (min_le_left _ _)
  have hy2 : dist y x < x := lt_of_lt_of_le hy (le_trans (min_le_right _ _) (min_le_left _ _))
  have hy3 : dist y x < 1 / 2 - x :=
    lt_of_lt_of_le hy (le_trans (min_le_right _ _) (min_le_right _ _))
  rw [Real.dist_eq, abs_lt] at hy2 hy3
  have hyy0 : (0 : ℝ) ≤ y := by linarith [hy2.1]
  have hyy : y ≤ 1 / 2 := by linarith [hy3.2]
  have hA := psi_sub_partial_le hyy0 hyy N
  have hB := psi_sub_partial_le (le_of_lt hx0) (le_of_lt hx) N
  have hC : dist (psiPartial N y) (psiPartial N x) < ε / 3 := hδ₁' hy1
  rw [Real.dist_eq] at hC ⊢
  have hsplit : psi y - psi x = (psi y - psiPartial N y)
      + (psiPartial N y - psiPartial N x) + (psiPartial N x - psi x) := by ring
  have habs : |psi y - psi x| ≤ |psi y - psiPartial N y| + |psiPartial N y - psiPartial N x|
      + |psiPartial N x - psi x| := by
    have t1 := abs_add_le (psi y - psiPartial N y) (psiPartial N y - psiPartial N x)
    have t2 := abs_add_le ((psi y - psiPartial N y) + (psiPartial N y - psiPartial N x))
      (psiPartial N x - psi x)
    rw [hsplit]
    linarith
  have hB' : |psiPartial N x - psi x| = |psi x - psiPartial N x| := abs_sub_comm _ _
  have hpow : (3 : ℝ) * (2 / 3 : ℝ) ^ N < ε / 3 := by linarith
  linarith [habs, hA, hB, hC, hB', hpow]
