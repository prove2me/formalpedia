-- Prove2me | solution 1 for BellSampling.Learn.stabSet_subspace
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-01T21:47:15.044216+00:00
-- url     : https://prove2.me/submissions/9d12dee1-ca64-4470-90a2-3537d9d24dda

import Mathlib
import Definitions.Def_StabilizerRank
import Definitions.Def_BellSampling_Learn_Setting
import Theorems.Thm_BellSampling_Learn_sigma_mul
import Theorems.Thm_BellSampling_Learn_bellProb_sum_eq_one
import Theorems.Thm_BellSampling_Learn_bell_outcome_uniform
open StabilizerRank
open BellSampling.Learn
set_option autoImplicit false

private lemma sigma1_zero : sigma1 (0, 0) = 1 := by
  ext a b
  cases a <;> cases b <;> simp [sigma1, sigma00, bitIdx]

private lemma sigma_zero (n : ℕ) : sigma (0 : PStr n) = 1 := by
  ext x y
  have h0 : ∀ i : Fin n, sigma1 ((0 : PStr n) i) (x i) (y i) = if x i = y i then 1 else 0 := by
    intro i
    have hs : (0 : PStr n) i = (0, 0) := rfl
    rw [hs, sigma1_zero]
    rfl
  simp_rw [sigma, Matrix.of_apply, h0]
  by_cases hxy : x = y
  · subst hxy
    simp
  · have h_ex : ∃ i : Fin n, x i ≠ y i := by
      by_contra h_all
      exact hxy (funext fun i => not_ne_iff.mp (fun hne => h_all ⟨i, hne⟩))
    rcases h_ex with ⟨i, hi⟩
    rw [Finset.prod_eq_zero (Finset.mem_univ i), Matrix.one_apply_ne hxy]
    exact if_neg hi

private lemma stabilizer_norm_sq_sum {n : ℕ} (ψ : QState n) (hψ : IsStabilizerState ψ) :
    ∑ x : Bits n, ‖ψ x‖ ^ 2 = 1 := by
  rcases hψ with ⟨U, ⟨hU_unit, _⟩, rfl⟩
  have hU : U.conjTranspose * U = 1 := Matrix.mem_unitaryGroup_iff'.mp hU_unit
  have hdot : star (U.mulVec (zeroState n)) ⬝ᵥ (U.mulVec (zeroState n)) = 1 := by
    rw [Matrix.star_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul, hU,
      Matrix.vecMul_one]
    simp [dotProduct, zeroState]
  have h_re : (star (U.mulVec (zeroState n)) ⬝ᵥ (U.mulVec (zeroState n))).re = 1 := by
    rw [hdot, Complex.one_re]
  have h_sum_re : (star (U.mulVec (zeroState n)) ⬝ᵥ (U.mulVec (zeroState n))).re =
      ∑ x : Bits n, ‖(U.mulVec (zeroState n)) x‖ ^ 2 := by
    simp only [dotProduct, Pi.star_apply, Complex.re_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    have hc : star ((U.mulVec (zeroState n)) x) * (U.mulVec (zeroState n)) x =
        ((‖(U.mulVec (zeroState n)) x‖ ^ 2 : ℝ) : ℂ) := by
      rw [← Complex.normSq_eq_norm_sq, Complex.star_def, Complex.normSq_eq_conj_mul_self]
    rw [hc, Complex.ofReal_re]
  linarith

theorem solution {n : ℕ} (ψ : QState n) (hψ : IsStabilizerState ψ) :
    ∃ W : Submodule (ZMod 2) (PStr n), (W : Set (PStr n)) = stabSet ψ ∧
      Module.finrank (ZMod 2) W = n := by
  classical
  have hzero : (0 : PStr n) ∈ stabSet ψ := by
    refine ⟨1, ?_⟩
    rw [sigma_zero, Matrix.one_mulVec, one_smul]
  have hadd : ∀ {s t : PStr n}, s ∈ stabSet ψ → t ∈ stabSet ψ → s + t ∈ stabSet ψ := by
    rintro s t ⟨c₁, hc₁⟩ ⟨c₂, hc₂⟩
    have hmulVec : (sigma s * sigma t).mulVec ψ = (c₁ * c₂) • ψ := by
      rw [← Matrix.mulVec_mulVec, hc₂, Matrix.mulVec_smul, hc₁, smul_smul, mul_comm]
    rcases BellSampling.Learn.sigma_mul s t with hst | hst
    · refine ⟨c₁ * c₂, ?_⟩
      rw [← hst, hmulVec]
    · refine ⟨-(c₁ * c₂), ?_⟩
      have hneg : (-sigma (s + t)).mulVec ψ = (c₁ * c₂) • ψ := by rw [← hst, hmulVec]
      rw [Matrix.neg_mulVec, neg_eq_iff_eq_neg] at hneg
      rw [hneg, neg_smul]
  let W : Submodule (ZMod 2) (PStr n) :=
    { carrier := stabSet ψ
      zero_mem' := hzero
      add_mem' := fun hs ht => hadd hs ht
      smul_mem' := by
        have hz : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide
        intro a t ht
        rcases hz a with rfl | rfl
        · rw [zero_smul]
          exact hzero
        · rw [one_smul]
          exact ht }
  refine ⟨W, rfl, ?_⟩
  obtain ⟨s, hs⟩ := BellSampling.Learn.bell_outcome_uniform ψ hψ
  have hsum1 : ∑ r : PStr n, bellProb ψ r = 1 :=
    BellSampling.Learn.bellProb_sum_eq_one ψ (stabilizer_norm_sq_sum ψ hψ)
  have hterm : ∀ r : PStr n,
      bellProb ψ r = if r + s ∈ W then (1 / 2 ^ n : ℝ) else 0 := by
    intro r
    by_cases hr : r + s ∈ W
    · rw [if_pos hr]
      exact (hs r).1 hr
    · rw [if_neg hr]
      exact (hs r).2 hr
  have h_equiv : (∑ r : PStr n, bellProb ψ r) =
      ∑ u : PStr n, if u ∈ W then (1 / 2 ^ n : ℝ) else 0 := by
    simp_rw [hterm]
    exact Equiv.sum_comp (Equiv.addRight s)
      (fun u : PStr n => if u ∈ W then (1 / 2 ^ n : ℝ) else 0)
  have h_sub : (∑ u : PStr n, if u ∈ W then (1 / 2 ^ n : ℝ) else 0) =
      ∑ _w : W, (1 / 2 ^ n : ℝ) := by
    rw [← Finset.sum_filter]
    exact Finset.sum_subtype (Finset.univ.filter fun u : PStr n => u ∈ W)
      (fun u => by simp) (fun _ => (1 / 2 ^ n : ℝ))
  have hcard_eq : Fintype.card W = 2 ^ n := by
    rw [h_equiv, h_sub, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one_div] at hsum1
    have h2n_ne : (2 : ℝ) ^ n ≠ 0 := by positivity
    have h_real : (Fintype.card W : ℝ) = ((2 ^ n : ℕ) : ℝ) := by
      rw [Nat.cast_pow, Nat.cast_ofNat]
      exact (div_eq_one_iff_eq h2n_ne).mp hsum1
    exact Nat.cast_injective h_real
  have hcard_finrank : Fintype.card W = 2 ^ Module.finrank (ZMod 2) W := by
    have hc := Module.card_eq_pow_finrank (K := ZMod 2) (V := W)
    simpa [ZMod.card] using hc
  rw [hcard_finrank] at hcard_eq
  exact Nat.pow_right_injective (by decide : 1 < 2) hcard_eq
