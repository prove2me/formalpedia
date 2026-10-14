-- Prove2me | solution 1 for ConstrNestedLogit.UpperBound.y_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-13T03:43:28.510035+00:00
-- url     : https://prove2.me/submissions/b4a47139-6aa2-4d1b-aadb-525a4f428691

import Mathlib
import Definitions.Def_NestedLogitVariants_General_Model
import Definitions.Def_NestedLogitVariants_General_Relaxation
import Definitions.Def_ConstrNestedLogit_UpperBound_Relaxation
import Definitions.Def_ConstrNestedLogit_UpperBound_LP13

open NestedLogitVariants.General
open ConstrNestedLogit.UpperBound

/-- Online Supplement A, proof of Proposition 7 (p. 33): if the vectors `X i` are feasible for
the linear programming relaxation of the knapsack problem (10) and include an optimal solution of
that relaxation for every `u ≥ 0`, then every feasible solution `(z, y)` of the linear program
(13) has `y_i ≥ 0` for every nest `i`. -/
theorem solution {ι : Type*} [Fintype ι] {n : ℕ} (I : Instance ι n)
    (hvnp : ∀ i, I.vnp i = 0) (hv : ∀ i j, 0 < I.v i j) (hγ : ∀ i, 0 < I.γ i)
    (w : ι → Fin n → ℝ) (c : ι → ℝ) (X : ι → Finset (Fin n → ℝ))
    (hw : ∀ i j, 0 < w i j) (hwc : ∀ i j, w i j ≤ c i)
    (hX : IsRelaxSolutionFamily I w c X) (z : ℝ) (y : ι → ℝ) (hzy : LP13Feasible I X z y) :
    ∀ i, 0 ≤ y i := by   classical
  intro i
  let u : ℝ := 1 + ∑ j, |I.r i j|
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have hur (j : Fin n) : I.r i j < u := by
    have hs := Finset.single_le_sum (fun k (_ : k ∈ Finset.univ) => abs_nonneg (I.r i k))
      (Finset.mem_univ j)
    dsimp [u]
    linarith [le_abs_self (I.r i j)]
  obtain ⟨x, hxX, hx⟩ := hX.2 i u hu
  have hxn (j : Fin n) : 0 ≤ x j := (hx.1.1 j (Set.mem_univ j)).1
  have hc : 0 ≤ c i := le_trans (Finset.sum_nonneg (fun j hj => mul_nonneg (hw i j).le (hxn j))) hx.1.2
  have hzero : RelaxFeasible w c i 0 := by
    constructor
    · intro j hj; simp
    · simpa using hc
  have ho := hx.2 0 hzero
  simp only [relaxObj, Pi.zero_apply, mul_zero, Finset.sum_const_zero] at ho
  have hn (j : Fin n) (_ : j ∈ Finset.univ) : I.v i j*(I.r i j-u)*x j ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos (hv i j).le (sub_nonpos.mpr (hur j).le)) (hxn j)
  have hs : (∑ j, I.v i j*(I.r i j-u)*x j) = 0 := le_antisymm (Finset.sum_nonpos hn) ho
  have hx0 : x = 0 := by
    funext j
    have hj := (Finset.sum_eq_zero_iff_of_nonpos hn).mp hs j (Finset.mem_univ j)
    exact (mul_eq_zero.mp hj).resolve_left (mul_ne_zero (ne_of_gt (hv i j)) (ne_of_lt (sub_neg.mpr (hur j))))
  rw [hx0] at hxX
  have hy := hzy.2 i 0 hxX
  simpa [F, hvnp i, Real.zero_rpow (ne_of_gt (hγ i))] using hy


