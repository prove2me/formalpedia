-- Prove2me | solution 1 for BellSampling.Learn.expect_eq_zero_of_not_mem
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-01T21:46:41.52409+00:00
-- url     : https://prove2.me/submissions/84436c1c-9210-400e-ad74-a1fad0fa9d0d

import Mathlib
import Definitions.Def_StabilizerRank
import Definitions.Def_BellSampling_Learn_Setting
open StabilizerRank
open BellSampling.Learn
set_option autoImplicit false

private abbrev aOf {n : ℕ} (t : PStr n) : Bits n := fun i => decide ((t i).2 = 1)
private abbrev bOf {n : ℕ} (t : PStr n) : Bits n := fun i => decide ((t i).1 = 1)

private lemma sigma1_eq_pauli1 (c : ZMod 2 × ZMod 2) (y x : Bool) :
    sigma1 c y x =
      (if c = (1, 1) then (-1 : ℂ) else 1) *
        (if y = xor (decide (c.2 = 1)) x then
          (if decide (c.1 = 1) && x then (-1 : ℂ) else 1)
        else 0) := by
  have hz : ∀ u : ZMod 2, u = 0 ∨ u = 1 := by decide
  have h01 : (0 : ZMod 2) ≠ 1 := by decide
  have h10 : (1 : ZMod 2) ≠ 0 := by decide
  rcases c with ⟨c1, c2⟩
  rcases hz c1 with rfl | rfl <;> rcases hz c2 with rfl | rfl <;>
    cases y <;> cases x <;>
    simp [sigma1, sigma00, sigma01, sigma10, sigma11_eq, bitIdx, h01, h10]

private lemma prod_neg_one_boole {α : Type*} [Fintype α] (p : α → Prop) [DecidablePred p] :
    (∏ i : α, if p i then (-1 : ℂ) else 1) = (-1 : ℂ) ^ (Finset.univ.filter p).card := by
  rw [Finset.prod_ite, Finset.prod_const_one, mul_one, Finset.prod_const]

private lemma sigma_eq_sign_smul_pauliMatrix {n : ℕ} (t : PStr n) :
    sigma t =
      ((-1 : ℂ) ^ (Finset.univ.filter fun i : Fin n => t i = (1, 1)).card) •
        pauliMatrix (aOf t) (bOf t) := by
  ext y x
  simp only [sigma, pauliMatrix, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul,
    sigma1_eq_pauli1, Finset.prod_mul_distrib]
  rw [prod_neg_one_boole (fun i : Fin n => t i = (1, 1))]
  congr 1
  by_cases hy : y = fun i => xor (aOf t i) (x i)
  · rw [if_pos hy]
    have hyi : ∀ i : Fin n, y i = xor (aOf t i) (x i) :=
      fun i => congr_fun hy i
    simp_rw [if_pos (hyi _)]
    exact prod_neg_one_boole (fun i : Fin n => bOf t i && x i)
  · rw [if_neg hy]
    have hex : ∃ i : Fin n, y i ≠ xor (aOf t i) (x i) := by
      by_contra hall
      exact hy (funext fun i => Classical.byContradiction fun hne => hall ⟨i, hne⟩)
    rcases hex with ⟨i, hi⟩
    exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)

private lemma neg_one_pow_mem_I_pow (k : ℕ) :
    ∃ c : Fin 4, (-1 : ℂ) ^ k = Complex.I ^ (c : ℕ) := by
  rcases Nat.even_or_odd k with ⟨m, rfl⟩ | ⟨m, rfl⟩
  · refine ⟨0, ?_⟩
    rw [← two_mul, pow_mul, neg_one_sq, one_pow]
    simp
  · refine ⟨2, ?_⟩
    rw [pow_add, pow_mul, neg_one_sq, one_pow, one_mul, pow_one]
    simp [Complex.I_sq]

private lemma sigma_mem_pauliGroupSet {n : ℕ} (t : PStr n) :
    sigma t ∈ pauliGroupSet n := by
  obtain ⟨c, hc⟩ := neg_one_pow_mem_I_pow (Finset.univ.filter fun i : Fin n => t i = (1, 1)).card
  refine ⟨c, aOf t, bOf t, ?_⟩
  rw [sigma_eq_sign_smul_pauliMatrix, hc]

private lemma pauliGroupSet_finite (n : ℕ) : (pauliGroupSet n).Finite := by
  have hsub : pauliGroupSet n =
      Set.range (fun p : Fin 4 × Bits n × Bits n =>
        Complex.I ^ (p.1 : ℕ) • pauliMatrix p.2.1 p.2.2) := by
    ext P
    simp only [pauliGroupSet, Set.mem_setOf_eq, Set.mem_range, Prod.exists, eq_comm]
  rw [hsub]
  exact Set.finite_range _

private lemma pauliMatrix_mulVec_zeroState {n : ℕ} (a b : Bits n) :
    (pauliMatrix a b).mulVec (zeroState n) = fun y => if y = a then 1 else 0 := by
  ext y
  simp only [Matrix.mulVec, dotProduct, pauliMatrix, Matrix.of_apply, zeroState,
    mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  simp

theorem solution {n : ℕ} (ψ : QState n) (hψ : IsStabilizerState ψ)
    (t : PStr n) (ht : t ∉ stabSet ψ) :
    ∑ x, star (ψ x) * ((sigma t).mulVec ψ) x = 0 := by
  rcases hψ with ⟨U, ⟨hU_unit, hU_norm⟩, rfl⟩
  have hU_left : U.conjTranspose * U = 1 := Matrix.mem_unitaryGroup_iff'.mp hU_unit
  have : Finite ↥(pauliGroupSet n) := (pauliGroupSet_finite n).to_subtype
  let f : ↥(pauliGroupSet n) → ↥(pauliGroupSet n) :=
    fun P => ⟨U * P.1 * star U, hU_norm P.1 P.2⟩
  have hf_inj : Function.Injective f := by
    intro P₁ P₂ h_eq
    ext1
    have hval : U * P₁.1 * U.conjTranspose = U * P₂.1 * U.conjTranspose :=
      congr_arg Subtype.val h_eq
    calc
      P₁.1 = (U.conjTranspose * U) * P₁.1 * (U.conjTranspose * U) := by
        rw [hU_left, Matrix.one_mul, Matrix.mul_one]
      _ = U.conjTranspose * (U * P₁.1 * U.conjTranspose) * U := by
        simp only [Matrix.mul_assoc]
      _ = U.conjTranspose * (U * P₂.1 * U.conjTranspose) * U := by rw [hval]
      _ = (U.conjTranspose * U) * P₂.1 * (U.conjTranspose * U) := by
        simp only [Matrix.mul_assoc]
      _ = P₂.1 := by rw [hU_left, Matrix.one_mul, Matrix.mul_one]
  have hf_surj : Function.Surjective f := Finite.surjective_of_injective hf_inj
  obtain ⟨⟨P, hP⟩, hP_eq⟩ := hf_surj ⟨sigma t, sigma_mem_pauliGroupSet t⟩
  have h_conj : U * P * U.conjTranspose = sigma t := congr_arg Subtype.val hP_eq
  rcases hP with ⟨c, a, b, rfl⟩
  have h_act : (sigma t).mulVec (U.mulVec (zeroState n)) =
      Complex.I ^ (c : ℕ) • U.mulVec (fun y => if y = a then 1 else 0) := by
    rw [← h_conj, Matrix.mulVec_mulVec, Matrix.mul_assoc, hU_left, Matrix.mul_one,
      Matrix.mul_smul, Matrix.smul_mulVec, ← Matrix.mulVec_mulVec, pauliMatrix_mulVec_zeroState]
  have ha_ne : a ≠ (fun _ => false) := by
    intro ha
    apply ht
    refine ⟨Complex.I ^ (c : ℕ), ?_⟩
    rw [h_act, ha]
    rfl
  change star (U.mulVec (zeroState n)) ⬝ᵥ ((sigma t).mulVec (U.mulVec (zeroState n))) = 0
  rw [h_act, Matrix.star_mulVec, dotProduct_smul, Matrix.dotProduct_mulVec,
    Matrix.vecMul_vecMul, hU_left, Matrix.vecMul_one]
  have h_dot_zero : star (zeroState n) ⬝ᵥ (fun y : Bits n => if y = a then (1 : ℂ) else 0) = 0 := by
    simp only [dotProduct, Pi.star_apply, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte, zeroState]
    rw [if_neg ha_ne, star_zero]
  rw [h_dot_zero, smul_zero]
