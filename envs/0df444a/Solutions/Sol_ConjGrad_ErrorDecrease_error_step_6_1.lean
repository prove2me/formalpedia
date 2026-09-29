-- Prove2me | solution 1 for ConjGrad.ErrorDecrease.error_step_6_1
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T03:24:29.15432+00:00
-- url     : https://prove2.me/submissions/bb26375f-4ff2-4527-938e-19395a59a00e

import Mathlib
import Definitions.Def_ConjGrad_ErrorDecrease_cgIter
import Definitions.Def_ConjGrad_ErrorDecrease_errorFun
import Definitions.Def_ConjGrad_ErrorDecrease_rayleigh

open Matrix

namespace ConjGrad.ErrorDecrease

lemma aux_es61_p0 {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosDef)
    (p : Fin n → ℝ) (h : p ⬝ᵥ (A *ᵥ p) = 0) : p = 0 := by
  by_contra hp
  have := hA.dotProduct_mulVec_pos hp
  simp only [star_trivial] at this
  linarith

lemma aux_es61_sym {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosDef)
    (u v : Fin n → ℝ) : u ⬝ᵥ (A *ᵥ v) = v ⬝ᵥ (A *ᵥ u) := by
  have hT : Aᵀ = A := by
    have := hA.isHermitian
    rw [IsHermitian, conjTranspose_eq_transpose_of_trivial] at this
    exact this
  rw [dotProduct_mulVec, ← mulVec_transpose, hT, dotProduct_comm]

lemma aux_es61_inv {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (k x₀ : Fin n → ℝ) (i : ℕ) :
    (cgIter A k x₀ i).r = k - A *ᵥ (cgIter A k x₀ i).x ∧
      (cgIter A k x₀ i).p ⬝ᵥ (cgIter A k x₀ i).r =
        (cgIter A k x₀ i).r ⬝ᵥ (cgIter A k x₀ i).r := by
  induction i with
  | zero => simp [cgIter]
  | succ i ih =>
    rw [cgIter.eq_2]
    set s := cgIter A k x₀ i with hs
    obtain ⟨ih1, ih2⟩ := ih
    refine ⟨?_, ?_⟩
    · simp only
      rw [ih1, mulVec_add, mulVec_smul]
      abel
    · simp only
      have hpr : s.p ⬝ᵥ (s.r - cgAlpha A s • (A *ᵥ s.p)) = 0 := by
        by_cases hq : s.p ⬝ᵥ (A *ᵥ s.p) = 0
        · rw [aux_es61_p0 hA s.p hq, zero_dotProduct]
        · rw [dotProduct_sub, dotProduct_smul, smul_eq_mul, ih2, cgAlpha,
            div_mul_cancel₀ _ hq, sub_self]
      rw [add_dotProduct, smul_dotProduct, hpr, smul_zero, add_zero]

theorem aux_es61_main {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (k x₀ h : Fin n → ℝ) (hh : A *ᵥ h = k) (i : ℕ) :
    errorFun A h (cgIter A k x₀ i).x - errorFun A h (cgIter A k x₀ (i + 1)).x =
        cgAlpha A (cgIter A k x₀ i) * ((cgIter A k x₀ i).r ⬝ᵥ (cgIter A k x₀ i).r) ∧
      cgAlpha A (cgIter A k x₀ i) * ((cgIter A k x₀ i).r ⬝ᵥ (cgIter A k x₀ i).r) =
        rayleigh A (cgIter A k x₀ i).p *
          (((cgIter A k x₀ i).x - (cgIter A k x₀ (i + 1)).x) ⬝ᵥ
            ((cgIter A k x₀ i).x - (cgIter A k x₀ (i + 1)).x)) := by
  obtain ⟨inv1, inv2⟩ := aux_es61_inv A hA k x₀ i
  rw [cgIter.eq_2]
  set s := cgIter A k x₀ i with hs
  simp only
  set a := cgAlpha A s with ha
  have hr : s.r = A *ᵥ (h - s.x) := by rw [inv1, mulVec_sub, hh]
  have hkey2 : a * (a * (s.p ⬝ᵥ (A *ᵥ s.p))) = a * (s.r ⬝ᵥ s.r) := by
    by_cases hq : s.p ⬝ᵥ (A *ᵥ s.p) = 0
    · have : a = 0 := by rw [ha, cgAlpha, hq, div_zero]
      simp [this]
    · congr 1
      rw [ha, cgAlpha]
      exact div_mul_cancel₀ _ hq
  refine ⟨?_, ?_⟩
  · unfold errorFun
    have e1 : h - (s.x + a • s.p) = (h - s.x) - a • s.p := by abel
    rw [e1]
    have hpe : s.p ⬝ᵥ (A *ᵥ (h - s.x)) = s.r ⬝ᵥ s.r := by rw [← hr, inv2]
    have hep : (h - s.x) ⬝ᵥ (A *ᵥ s.p) = s.r ⬝ᵥ s.r := by
      rw [aux_es61_sym hA, hpe]
    generalize h - s.x = e at hpe hep ⊢
    simp only [mulVec_sub, mulVec_smul, sub_dotProduct, dotProduct_sub, smul_dotProduct,
      dotProduct_smul, smul_eq_mul]
    rw [hpe, hep]
    linarith [hkey2]
  · have e2 : s.x - (s.x + a • s.p) = -(a • s.p) := by abel
    rw [e2, neg_dotProduct_neg, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul]
    by_cases hp : s.p = 0
    · have : s.r ⬝ᵥ s.r = 0 := by rw [← inv2, hp, zero_dotProduct]
      simp [this, hp, rayleigh]
    · have hpp : s.p ⬝ᵥ s.p ≠ 0 := by
        intro h0
        exact hp (dotProduct_self_eq_zero.mp h0)
      rw [rayleigh]
      rw [← hkey2]
      field_simp

end ConjGrad.ErrorDecrease

open ConjGrad.ErrorDecrease
open Matrix

theorem solution {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (k x₀ h : Fin n → ℝ) (hh : A *ᵥ h = k) (i : ℕ) :
    errorFun A h (cgIter A k x₀ i).x - errorFun A h (cgIter A k x₀ (i + 1)).x =
        cgAlpha A (cgIter A k x₀ i) * ((cgIter A k x₀ i).r ⬝ᵥ (cgIter A k x₀ i).r) ∧
      cgAlpha A (cgIter A k x₀ i) * ((cgIter A k x₀ i).r ⬝ᵥ (cgIter A k x₀ i).r) =
        rayleigh A (cgIter A k x₀ i).p *
          (((cgIter A k x₀ i).x - (cgIter A k x₀ (i + 1)).x) ⬝ᵥ
            ((cgIter A k x₀ i).x - (cgIter A k x₀ (i + 1)).x)) :=
  aux_es61_main A hA k x₀ h hh i
