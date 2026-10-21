-- Prove2me | solution 1 for FuzzyExtractors.EditSketch.appendix_E_ratio_unique
-- status  : ACCEPTED   (prove)
-- author  : @涼宮 ハルヒ
-- created : 2026-10-20T08:24:30.023277+00:00
-- url     : https://prove2.me/submissions/4a63b42b-171f-4e41-a160-1344fb333a7d

import Definitions.Def_FuzzyExtractors_EditSketch_Basic
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Algebra.CharP.Defs
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

noncomputable section
open Polynomial
open FuzzyExtractors.EditSketch

private lemma locator_degree {K : Type} [Field K] (M : Finset Kˣ) :
    (sigma M).natDegree ≤ M.card := by
  unfold sigma
  calc
    _ ≤ ∑ x ∈ M, (1 - C (x : K) * X).natDegree := natDegree_prod_le _ _
    _ ≤ ∑ _x ∈ M, 1 := by
      apply Finset.sum_le_sum
      intro x hx
      apply (natDegree_sub_le _ _).trans
      simp only [max_le_iff, natDegree_one, zero_le, true_and]
      exact (natDegree_mul_le (p := C (x : K)) (q := X)).trans (by simp)
    _ = M.card := by simp

private lemma evaluator_degree {K : Type} [Field K] [DecidableEq K]
    (M : Finset Kˣ) : (omega M).natDegree ≤ M.card := by
  unfold omega
  apply natDegree_sum_le_of_forall_le
  intro x hx
  have hprod := locator_degree (M.erase x)
  have hxcard := Finset.card_erase_add_one hx
  change (C (x : K) * X * sigma (M.erase x)).natDegree ≤ M.card
  calc
    _ ≤ (C (x : K) * X).natDegree + (sigma (M.erase x)).natDegree :=
      natDegree_mul_le
    _ ≤ 1 + (M.erase x).card := by
      exact Nat.add_le_add
        ((natDegree_mul_le (p := C (x : K)) (q := X)).trans (by simp)) hprod
    _ ≤ M.card := by omega

private lemma truncated_geometric {K : Type} [Field K] (a : K) (δ : ℕ) (hδ : 1 ≤ δ) :
    (∑ l ∈ Finset.Icc 1 (δ - 1), C (a ^ l) * X ^ l) * (1 - C a * X) =
      C a * X - (C a * X) ^ δ := by
  have hinterval : Finset.Icc 1 (δ - 1) = Finset.Ico 1 δ := by
    ext l
    simp only [Finset.mem_Icc, Finset.mem_Ico]
    omega
  rw [hinterval]
  have hpow (l : ℕ) : C (a ^ l) * X ^ l = (C a * X) ^ l := by
    rw [mul_pow, map_pow]
  simp_rw [hpow]
  rw [Finset.sum_Ico_eq_sub _ hδ]
  simp only [Finset.sum_range_one, pow_zero]
  rw [sub_mul, geom_sum_mul_neg]
  ring

private lemma key_equation_from_definitions {K : Type} [Field K] [DecidableEq K]
    (δ : ℕ) (hδ : 1 ≤ δ) (M : Finset Kˣ) :
    X ^ δ ∣ synPoly δ M * sigma M - omega M := by
  have hsyn : synPoly δ M = ∑ x ∈ M,
      ∑ l ∈ Finset.Icc 1 (δ - 1), C ((x : K) ^ l) * X ^ l := by
    unfold synPoly syn
    simp only [map_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
  rw [hsyn, omega, Finset.sum_mul, ← Finset.sum_sub_distrib]
  apply Finset.dvd_sum
  intro x hx
  change X ^ δ ∣
    (∑ l ∈ Finset.Icc 1 (δ - 1), C ((x : K) ^ l) * X ^ l) * sigma M -
      C (x : K) * X * sigma (M.erase x)
  have hfactor : sigma M =
      (1 - C (x : K) * X) * sigma (M.erase x) := by
    unfold sigma
    exact (Finset.mul_prod_erase M (fun y => (1 - C (y : K) * X)) hx).symm
  rw [hfactor, ← mul_assoc, truncated_geometric (x : K) δ hδ]
  refine ⟨-(C (x : K) ^ δ * sigma (M.erase x)), ?_⟩
  rw [mul_pow]
  ring

theorem solution {K : Type} [Field K] [Fintype K] [DecidableEq K] [CharP K 2]
    (δ : ℕ) (hδ : 1 ≤ δ) (M : Finset Kˣ) (hM : M.card ≤ (δ - 1) / 2)
    (σ' ω' : K[X]) (hσ' : σ' ≠ 0)
    (hdegσ : σ'.natDegree ≤ (δ - 1) / 2) (hdegω : ω'.natDegree ≤ (δ - 1) / 2)
    (hcong : X ^ δ ∣ synPoly δ M * σ' - ω') :
    omega M * σ' = sigma M * ω' := by
  have hcanonical := key_equation_from_definitions δ hδ M
  have hdiv : X ^ δ ∣ omega M * σ' - sigma M * ω' := by
    have h := dvd_sub (dvd_mul_of_dvd_right hcong (sigma M))
      (dvd_mul_of_dvd_right hcanonical σ')
    convert h using 1 <;> ring
  have hdeg : (omega M * σ' - sigma M * ω').natDegree < δ := by
    have hs := locator_degree M
    have hw := evaluator_degree M
    have hd1 := natDegree_mul_le (p := omega M) (q := σ')
    have hd2 := natDegree_mul_le (p := sigma M) (q := ω')
    have hd3 := natDegree_sub_le (omega M * σ') (sigma M * ω')
    have hhalf : 2 * ((δ - 1) / 2) ≤ δ - 1 := Nat.mul_div_le (δ - 1) 2
    omega
  exact sub_eq_zero.mp (eq_zero_of_dvd_of_natDegree_lt hdiv (by simpa using hdeg))

#print axioms solution
