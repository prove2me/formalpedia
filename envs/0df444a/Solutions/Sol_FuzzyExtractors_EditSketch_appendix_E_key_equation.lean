-- Prove2me | solution 1 for FuzzyExtractors.EditSketch.appendix_E_key_equation
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-23T15:21:15.265327+00:00
-- url     : https://prove2.me/submissions/77ac0071-ea83-4de7-9a72-c4a3bfa887f1

import Mathlib
import Definitions.Def_FuzzyExtractors_EditSketch_Basic
open Polynomial FuzzyExtractors.EditSketch
open scoped BigOperators
namespace KeyEquation
lemma syndrome_split {K : Type} [Field K] (δ : ℕ) (M : Finset Kˣ) :
    synPoly δ M = ∑ x ∈ M, ∑ l ∈ Finset.Icc 1 (δ-1), (C (x : K) * X)^l := by
  unfold synPoly syn
  simp only [map_sum,Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x hx
  simp only [map_pow,mul_pow]
lemma geometric {K : Type} [Field K] (δ : ℕ) (hδ : 0 < δ) (x : K) :
    (∑ l ∈ Finset.Icc 1 (δ-1), (C x * X)^l) * (1-C x*X) = C x*X-(C x*X)^δ := by
  have hs : Finset.Icc 1 (δ-1) = Finset.Ico 1 δ := by
    ext i
    simp only [Finset.mem_Icc,Finset.mem_Ico]
    omega
  rw [hs]
  simpa using geom_sum_Ico_mul_neg (C x * X) (show 1 ≤ δ by omega)
lemma key_equation {K : Type} [Field K] [DecidableEq K] (δ : ℕ) (M : Finset Kˣ) :
    X^δ ∣ synPoly δ M * sigma M - omega M := by
  classical
  by_cases hδ : δ = 0
  · simp [hδ]
  · rw [syndrome_split,Finset.sum_mul,omega,← Finset.sum_sub_distrib]
    apply Finset.dvd_sum
    intro x hx
    have hs : sigma M = (1-C (x : K)*X) * ∏ y ∈ M.erase x, (1-C (y : K)*X) := by
      exact (Finset.mul_prod_erase M (fun y => 1-C (y : K)*X) hx).symm
    rw [hs,← mul_assoc,geometric δ (by omega)]
    refine ⟨-(C (x : K)^δ * ∏ y ∈ M.erase x, (1-C (y : K)*X)),?_⟩
    rw [mul_pow]
    ring
end KeyEquation

theorem solution {K : Type} [Field K] [Fintype K] [DecidableEq K] [CharP K 2]
    (δ : ℕ) (M : Finset Kˣ) :
    X ^ δ ∣ synPoly δ M * sigma M - omega M := KeyEquation.key_equation δ M
#print axioms solution
