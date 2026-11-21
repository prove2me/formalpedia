-- Prove2me | solution 1 for GRH.liouville_reduced_progression_squarefree_bilinear_bound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @pragyan
-- created : 2026-11-21T01:18:19.019416+00:00
-- url     : https://prove2.me/submissions/1ac3977b-b21f-475c-9a0a-d2b67ee885f6
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_GRH_SquarefreeBilinear
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Theorems.Thm_GRH_reduced_liouville_harmonic_power_decay
import Theorems.Thm_GRH_centered_squarefree_liouville_bilinear_power_bound

open scoped BigOperators
open Finset

private theorem factored_sum {α : Type*} (s : Finset α) (l h : α → ℝ) (K : ℝ) :
    (∑ d ∈ s, l d * ∑ e ∈ s, l e * (K * h d * h e)) =
      K * (∑ d ∈ s, l d * h d) ^ 2 := by
  rw [pow_two, Finset.sum_mul_sum]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  apply Finset.sum_congr rfl
  intro e he
  ring

private theorem centered_sum {α : Type*} (s : Finset α) (l h : α → ℝ)
    (A : α → α → ℝ) (K : ℝ) :
    (∑ d ∈ s, l d * ∑ e ∈ s, l e * A d e) =
      (∑ d ∈ s, l d * ∑ e ∈ s, l e * (A d e - K * h d * h e)) +
        K * (∑ d ∈ s, l d * h d) ^ 2 := by
  simp only [mul_sub, Finset.sum_sub_distrib]
  rw [factored_sum]
  ring


theorem GRH.squarefree_bilinear_eq_centered
    (q : ℕ) [NeZero q] (a : ZMod q) (N : ℕ) :
    (∑ d ∈ Finset.Ioc 0 N.sqrt, (ArithmeticFunction.liouville d : ℝ) *
      ∑ e ∈ Finset.Ioc 0 N.sqrt, (ArithmeticFunction.liouville e : ℝ) *
        (((Finset.Ioc 0 (N / (d * e))).filter
          (fun r => Squarefree r ∧ ((d * e * r : ℕ) : ZMod q) = a)).card : ℝ)) =
      GRH.centeredSquarefreeBilinear q a N +
        GRH.squarefreeProgressionDensity q * (N : ℝ) *
          (GRH.reducedLiouvilleHarmonic q N.sqrt) ^ 2 := by
  classical
  let h : ℕ → ℝ := fun d => if IsUnit (d : ZMod q) then 1 / (d : ℝ) else 0
  have harmonic :
      (∑ d ∈ Finset.Ioc 0 N.sqrt, (ArithmeticFunction.liouville d : ℝ) * h d) =
        GRH.reducedLiouvilleHarmonic q N.sqrt := by
    unfold GRH.reducedLiouvilleHarmonic
    apply Finset.sum_congr rfl
    intro d hd
    by_cases hu : IsUnit (d : ZMod q) <;> simp [h, hu, div_eq_mul_inv]
  have kernel (d e : ℕ) :
      (if IsUnit (d : ZMod q) ∧ IsUnit (e : ZMod q) then
        GRH.squarefreeProgressionDensity q * (N : ℝ) / ((d : ℝ) * (e : ℝ)) else 0) =
      (GRH.squarefreeProgressionDensity q * (N : ℝ)) * h d * h e := by
    by_cases hd : IsUnit (d : ZMod q) <;> by_cases he : IsUnit (e : ZMod q) <;>
      simp [h, hd, he, div_eq_mul_inv, mul_inv_rev] <;> ring
  change (∑ d ∈ Finset.Ioc 0 N.sqrt, (ArithmeticFunction.liouville d : ℝ) *
      ∑ e ∈ Finset.Ioc 0 N.sqrt, (ArithmeticFunction.liouville e : ℝ) *
        GRH.squarefreeProgressionCount q a N d e) = _
  unfold GRH.centeredSquarefreeBilinear
  simp_rw [kernel]
  rw [← harmonic]
  exact centered_sum (Finset.Ioc 0 N.sqrt)
    (fun d => (ArithmeticFunction.liouville d : ℝ)) h
    (GRH.squarefreeProgressionCount q a N) (GRH.squarefreeProgressionDensity q * (N : ℝ))


namespace GRH

lemma sqrt_rpow_weight_bound (N : ℕ) (σ : ℝ) (hone : σ < 1) :
    (N : ℝ) * (((N.sqrt : ℝ) + 1) ^ (σ - 1)) ^ 2 ≤ ((N : ℝ) + 1) ^ σ := by
  have hN : 0 ≤ (N : ℝ) := Nat.cast_nonneg N
  have hU : 0 < (N.sqrt : ℝ) + 1 := by positivity
  have hX : 0 < (N : ℝ) + 1 := by positivity
  have hsqrt : (N : ℝ) + 1 ≤ ((N.sqrt : ℝ) + 1) ^ 2 := by
    have h := Nat.lt_succ_sqrt' N
    have h' : N + 1 ≤ (N.sqrt + 1) ^ 2 := by simpa [Nat.succ_eq_add_one] using Nat.succ_le_iff.mpr h
    exact_mod_cast h'
  have hp : (((N.sqrt : ℝ) + 1) ^ (σ - 1)) ^ 2 ≤
      ((N : ℝ) + 1) ^ (σ - 1) := by
    have h := Real.rpow_le_rpow_of_nonpos hX hsqrt (by linarith : σ - 1 ≤ 0)
    rw [← Real.rpow_natCast_mul hU.le] at h
    rw [← Real.rpow_mul_natCast hU.le]
    convert h using 1 <;> congr 1 <;> ring
  calc
    (N : ℝ) * (((N.sqrt : ℝ) + 1) ^ (σ - 1)) ^ 2
        ≤ (N : ℝ) * (((N : ℝ) + 1) ^ (σ - 1)) := mul_le_mul_of_nonneg_left hp hN
    _ ≤ ((N : ℝ) + 1) * (((N : ℝ) + 1) ^ (σ - 1)) :=
      mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg hX.le _)
    _ = ((N : ℝ) + 1) ^ σ := by
      nth_rw 1 [← Real.rpow_one ((N : ℝ) + 1)]
      rw [← Real.rpow_add hX]
      congr 1
      ring

lemma harmonic_main_weight_bound (N : ℕ) (σ K x : ℝ) (hone : σ < 1)
    (hK : 0 ≤ K) (hx : |x| ≤ K * ((N.sqrt : ℝ) + 1) ^ (σ - 1)) :
    (N : ℝ) * x ^ 2 ≤ K ^ 2 * ((N : ℝ) + 1) ^ σ := by
  have hs : x ^ 2 ≤ K ^ 2 * (((N.sqrt : ℝ) + 1) ^ (σ - 1)) ^ 2 := by
    have h := sq_le_sq₀ (abs_nonneg x) (by positivity : 0 ≤ K * ((N.sqrt : ℝ) + 1) ^ (σ - 1))
    have := h.mpr hx
    simpa only [sq_abs, mul_pow] using this
  calc
    (N : ℝ) * x ^ 2 ≤ (N : ℝ) *
        (K ^ 2 * (((N.sqrt : ℝ) + 1) ^ (σ - 1)) ^ 2) :=
      mul_le_mul_of_nonneg_left hs (Nat.cast_nonneg N)
    _ = K ^ 2 * ((N : ℝ) * (((N.sqrt : ℝ) + 1) ^ (σ - 1)) ^ 2) := by ring
    _ ≤ K ^ 2 * ((N : ℝ) + 1) ^ σ :=
      mul_le_mul_of_nonneg_left (sqrt_rpow_weight_bound N σ hone) (sq_nonneg K)

end GRH

theorem solution
    (q : ℕ) [NeZero q] (σ : ℝ) (hhalf : 1 / 2 < σ) (hone : σ < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a : ZMod q, IsUnit a → ∀ N : ℕ,
      |∑ d ∈ Finset.Ioc 0 N.sqrt, (ArithmeticFunction.liouville d : ℝ) *
        ∑ e ∈ Finset.Ioc 0 N.sqrt, (ArithmeticFunction.liouville e : ℝ) *
          (((Finset.Ioc 0 (N / (d * e))).filter
            (fun r => Squarefree r ∧ ((d * e * r : ℕ) : ZMod q) = a)).card : ℝ)|
        ≤ C * ((N : ℝ) + 1) ^ σ := by

  obtain ⟨K, hK, hH⟩ := GRH.reduced_liouville_harmonic_power_decay q σ hhalf hone
  obtain ⟨D, hD, hE⟩ := GRH.centered_squarefree_liouville_bilinear_power_bound q σ hhalf hone
  refine ⟨|GRH.squarefreeProgressionDensity q| * K ^ 2 + D, by positivity, ?_⟩
  intro a ha N
  rw [GRH.squarefree_bilinear_eq_centered]
  calc
    |GRH.centeredSquarefreeBilinear q a N +
        GRH.squarefreeProgressionDensity q * (N : ℝ) *
          (GRH.reducedLiouvilleHarmonic q N.sqrt) ^ 2|
      ≤ |GRH.centeredSquarefreeBilinear q a N| +
        |GRH.squarefreeProgressionDensity q * (N : ℝ) *
          (GRH.reducedLiouvilleHarmonic q N.sqrt) ^ 2| := abs_add_le _ _
    _ ≤ D * ((N : ℝ) + 1) ^ σ +
        |GRH.squarefreeProgressionDensity q| *
          ((N : ℝ) * (GRH.reducedLiouvilleHarmonic q N.sqrt) ^ 2) := by
      have hnabs : |(N : ℝ)| = (N : ℝ) := abs_of_nonneg (Nat.cast_nonneg N)
      have hsabs : |(GRH.reducedLiouvilleHarmonic q N.sqrt) ^ 2| =
          (GRH.reducedLiouvilleHarmonic q N.sqrt) ^ 2 := abs_of_nonneg (sq_nonneg _)
      simp only [abs_mul, hnabs, hsabs]
      exact add_le_add (hE a ha N) (le_of_eq (mul_assoc _ _ _))
    _ ≤ D * ((N : ℝ) + 1) ^ σ +
        |GRH.squarefreeProgressionDensity q| * (K ^ 2 * ((N : ℝ) + 1) ^ σ) := by
      exact add_le_add_right (mul_le_mul_of_nonneg_left
        (GRH.harmonic_main_weight_bound N σ K _ hone hK (hH N.sqrt))
        (abs_nonneg _)) _
    _ = (|GRH.squarefreeProgressionDensity q| * K ^ 2 + D) * ((N : ℝ) + 1) ^ σ := by ring
