-- Prove2me | solution 1 for DissipativePrep.Unique.dark_jumpOps
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-21T22:00:19.52306+00:00
-- url     : https://prove2.me/submissions/68d2e773-6b6e-481a-a147-1708fc7c8786

import Mathlib
import Definitions.Def_DissipativePrep_Unique_Model

open scoped Matrix ComplexConjugate
open QAlgorithms QAlgorithms.Papers.Independent.Dependency50.P16 DissipativePrep.Unique

lemma lowerQ_mulVec {n : ℕ} (k : Fin n) (χ : Qubits n → ℂ) (x : Qubits n) :
    (lowerQ k *ᵥ χ) x = if x k = false then χ (Function.update x k true) else 0 := by
  classical
  simp only [Matrix.mulVec, dotProduct, lowerQ, Matrix.of_apply, ite_mul, one_mul, zero_mul]
  split_ifs with hx
  · rw [Finset.sum_eq_single (Function.update x k true)]
    · rw [if_pos]; refine ⟨by simp, ?_⟩
      funext i; by_cases hi : i = k
      · subst hi; simp [hx]
      · simp [hi]
    · intro y _ hy
      rw [if_neg]; rintro ⟨hyk, rfl⟩
      apply hy; funext i; by_cases hi : i = k
      · subst hi; simp [hyk]
      · simp [hi]
    · simp
  · apply Finset.sum_eq_zero
    intro y _
    rw [if_neg]; rintro ⟨_, rfl⟩
    exact hx (by simp)

lemma kerQ {n : ℕ} (χ : Qubits n → ℂ) :
    (∀ k, lowerQ k *ᵥ χ = 0) ↔ ∀ y : Qubits n, y ≠ (fun _ => false) → χ y = 0 := by
  classical
  constructor
  · intro h y hy
    obtain ⟨k, hk⟩ : ∃ k, y k = true := by
      by_contra hc; push_neg at hc; apply hy; funext i; simpa using hc i
    have := congrFun (h k) (Function.update y k false)
    rw [lowerQ_mulVec] at this
    simp only [Function.update_self, if_true, Function.update_idem] at this
    rwa [show Function.update y k true = y by rw [← hk]; exact Function.update_eq_self k y] at this
  · intro h k
    funext x
    rw [lowerQ_mulVec]
    split_ifs with hx
    · apply h; intro he
      have := congrFun he k; simp at this
    · rfl

lemma lower_mulVec {n : ℕ} (k : Fin n) (v : Fin (2 ^ n) → ℂ) :
    lower k *ᵥ v = fun i => (lowerQ k *ᵥ (v ∘ bitsEquivFin n)) ((bitsEquivFin n).symm i) := by
  funext i
  simp only [lower, Matrix.mulVec, dotProduct, Matrix.reindex_apply, Matrix.submatrix_apply,
    Function.comp_apply]
  exact Fintype.sum_equiv (bitsEquivFin n).symm _ _ (fun j => by simp)

lemma e_zero (n : ℕ) : bitsEquivFin n (fun _ => false) = 0 := by
  ext; rw [bitsEquivFin_apply]; simp [bitsToNat]

theorem solution {n : ℕ} (U : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin (2 ^ n)) ℂ) (φ : EuclideanSpace ℂ (Fin (2 ^ n))) :
    (∀ k, act (jumpOps U k) φ = 0) ↔ ∃ a : ℂ, φ = a • target U := by
  classical
  have h1 : U * Uᴴ = 1 := Matrix.mem_unitaryGroup_iff.mp hU
  have h2 : Uᴴ * U = 1 := Matrix.mem_unitaryGroup_iff'.mp hU
  set v := WithLp.ofLp φ with hv
  set χ := Uᴴ *ᵥ v with hχ
  have hvχ : v = U *ᵥ χ := by rw [hχ, Matrix.mulVec_mulVec, h1, Matrix.one_mulVec]
  have inj : ∀ w, U *ᵥ w = 0 ↔ w = 0 := by
    intro w; constructor
    · intro h; have := congrArg (Uᴴ *ᵥ ·) h
      simpa [Matrix.mulVec_mulVec, h2] using this
    · rintro rfl; simp
  have step1 : (∀ k, act (jumpOps U k) φ = 0) ↔ ∀ k, lower k *ᵥ χ = 0 := by
    refine forall_congr' fun k => ?_
    rw [← inj, hχ, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
    unfold act jumpOps
    constructor
    · intro h; have := congrArg WithLp.ofLp h; simpa using this
    · intro h; rw [h]; rfl
  have step2 : (∀ k, lower k *ᵥ χ = 0) ↔ ∀ i, i ≠ 0 → χ i = 0 := by
    have : (∀ k, lower k *ᵥ χ = 0) ↔ ∀ k, lowerQ k *ᵥ (χ ∘ bitsEquivFin n) = 0 := by
      refine forall_congr' fun k => ?_
      rw [lower_mulVec]
      constructor
      · intro h; funext y; have := congrFun h (bitsEquivFin n y); simpa using this
      · intro h; rw [h]; rfl
    rw [this, kerQ]
    constructor
    · intro h i hi
      have := h ((bitsEquivFin n).symm i) (by
        intro he; apply hi; rw [← e_zero n, ← he]; simp)
      simpa using this
    · intro h y hy
      apply h; intro he; apply hy
      apply (bitsEquivFin n).injective; rw [he, e_zero]
  rw [step1, step2]
  constructor
  · intro h
    refine ⟨χ 0, ?_⟩
    have hχs : χ = χ 0 • Pi.single 0 1 := by
      funext i; by_cases hi : i = 0
      · subst hi; simp
      · simp [hi, h i hi]
    apply WithLp.ofLp_injective
    rw [← hv, hvχ, hχs]
    simp [target, act, ket, Matrix.mulVec_smul]
  · rintro ⟨a, ha⟩ i hi
    have : χ = a • Pi.single 0 1 := by
      rw [hχ, hv, ha]
      have hc : Uᴴ *ᵥ U.col 0 = Pi.single 0 1 := by
        rw [← Matrix.mulVec_single_one, Matrix.mulVec_mulVec, h2, Matrix.one_mulVec]
      simp [target, act, ket, Matrix.mulVec_smul, hc]
    rw [this]; simp [hi]
