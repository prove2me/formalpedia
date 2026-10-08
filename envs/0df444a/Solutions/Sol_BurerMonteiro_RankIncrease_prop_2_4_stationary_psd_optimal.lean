-- Prove2me | solution 1 for BurerMonteiro.RankIncrease.prop_2_4_stationary_psd_optimal
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-05T04:46:08.514346+00:00
-- url     : https://prove2.me/submissions/bef287d1-b231-402d-a627-61b55bc7b0b9

import Mathlib
import Definitions.Def_BurerMonteiro_RankIncrease_SDP
import Definitions.Def_BurerMonteiro_RankIncrease_Nr

set_option autoImplicit false

open Matrix
open scoped Matrix.Norms.Frobenius

open BurerMonteiro.RankIncrease in
theorem p9b_frob_nonneg {n : ℕ} {S X : Matrix (Fin n) (Fin n) ℝ} (hS : S.PosSemidef)
    (hX : X.PosSemidef) : 0 ≤ frob S X := by
  have h := (hS.hadamard hX).dotProduct_mulVec_nonneg (fun _ => (1:ℝ))
  have e : frob S X = star (fun _ : Fin n => (1:ℝ)) ⬝ᵥ ((S ⊙ X) *ᵥ fun _ => (1:ℝ)) := by
    simp only [frob, trace, diag, Matrix.mul_apply, transpose_apply, dotProduct, mulVec,
      hadamard_apply, star_one, Pi.star_apply, one_mul, mul_one]
    exact Finset.sum_comm
  rw [e]; exact h

open BurerMonteiro.RankIncrease in
theorem p9b_frob_slack {n m : ℕ} (C : Matrix (Fin n) (Fin n) ℝ)
    (A : Fin m → Matrix (Fin n) (Fin n) ℝ) (y : Fin m → ℝ) (X : Matrix (Fin n) (Fin n) ℝ) :
    frob (slack C A y) X = frob C X - ∑ i, y i * frob (A i) X := by
  simp [frob, slack, Matrix.transpose_sub, Matrix.transpose_sum, Matrix.sub_mul,
    Matrix.sum_mul, Matrix.trace_sub, Matrix.trace_sum, Matrix.trace_smul]

open BurerMonteiro.RankIncrease in
theorem p9b_frob_feas {n m : ℕ} (C : Matrix (Fin n) (Fin n) ℝ)
    (A : Fin m → Matrix (Fin n) (Fin n) ℝ) (b y : Fin m → ℝ) (X : Matrix (Fin n) (Fin n) ℝ)
    (hX : ∀ i, frob (A i) X = b i) :
    frob C X = frob (slack C A y) X + b ⬝ᵥ y := by
  rw [p9b_frob_slack]
  simp only [hX, dotProduct]
  have : ∑ i, y i * b i = ∑ i, b i * y i := Finset.sum_congr rfl fun i _ => mul_comm _ _
  rw [this]; ring

open BurerMonteiro.RankIncrease in
theorem p9b_frob_smul_right {n : ℕ} (S X : Matrix (Fin n) (Fin n) ℝ) (c : ℝ) :
    frob S (c • X) = c * frob S X := by
  simp [frob, Matrix.trace_smul]

open BurerMonteiro.RankIncrease in
theorem p9b_lag_eq {n m r : ℕ} (C : Matrix (Fin n) (Fin n) ℝ)
    (A : Fin m → Matrix (Fin n) (Fin n) ℝ) (b y : Fin m → ℝ) (R : Matrix (Fin n) (Fin r) ℝ) :
    lagrangian C A b R y = frob (slack C A y) (R * Rᵀ) + b ⬝ᵥ y := by
  rw [lagrangian, p9b_frob_slack]
  simp only [mul_sub, Finset.sum_sub_distrib, dotProduct]
  have : ∑ i, y i * b i = ∑ i, b i * y i := Finset.sum_congr rfl fun i _ => mul_comm _ _
  rw [this]; ring

open BurerMonteiro.RankIncrease in
theorem p9b_stat_zero {n m r : ℕ} (C : Matrix (Fin n) (Fin n) ℝ)
    (A : Fin m → Matrix (Fin n) (Fin n) ℝ) (b y : Fin m → ℝ) (R : Matrix (Fin n) (Fin r) ℝ)
    (hstat : IsStationary C A b R y) : frob (slack C A y) (R * Rᵀ) = 0 := by
  set a := frob (slack C A y) (R * Rᵀ) with ha
  have hf : HasDerivAt (fun t : ℝ => R + t • R) ((1:ℝ) • R) 0 :=
    ((hasDerivAt_id (0:ℝ)).smul_const R).const_add R
  have hst : HasFDerivAt (fun R' => lagrangian C A b R' y)
      (0 : Matrix (Fin n) (Fin r) ℝ →L[ℝ] ℝ) ((fun t : ℝ => R + t • R) 0) := by
    simpa using hstat.2
  have h1 : HasDerivAt (fun t : ℝ => lagrangian C A b (R + t • R) y) 0 0 := by
    have := hst.comp_hasDerivAt (0:ℝ) hf
    exact this
  have hfun : (fun t : ℝ => lagrangian C A b (R + t • R) y)
      = fun t : ℝ => (1 + t) ^ 2 * a + b ⬝ᵥ y := by
    funext t
    rw [p9b_lag_eq]
    have : (R + t • R) * (R + t • R)ᵀ = ((1 + t) ^ 2) • (R * Rᵀ) := by
      have e : R + t • R = (1 + t) • R := by rw [add_smul, one_smul]
      rw [e, transpose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, sq]
    rw [this, p9b_frob_smul_right]
  have h2 : HasDerivAt (fun t : ℝ => (1 + t) ^ 2 * a + b ⬝ᵥ y) (2 * a) 0 := by
    have := ((((hasDerivAt_id (0:ℝ)).const_add 1).pow 2).mul_const a).add_const (b ⬝ᵥ y)
    simpa using this
  rw [hfun] at h1
  have := h1.unique h2
  linarith

open Matrix BurerMonteiro.RankIncrease in
theorem solution {n m : ℕ} (C : Matrix (Fin n) (Fin n) ℝ)
    (A : Fin m → Matrix (Fin n) (Fin n) ℝ) (b : Fin m → ℝ) (hC : C.IsSymm)
    (hA : ∀ i, (A i).IsSymm) (hsa : StandingAssumptions C A b) {r : ℕ} (hr0 : 0 < r)
    (hrn : r ≤ n) (R : Matrix (Fin n) (Fin r) ℝ) (y : Fin m → ℝ)
    (hstat : IsStationary C A b R y) (hS : (slack C A y).PosSemidef) :
    IsPrimalOptimal C A b (R * Rᵀ) ∧ IsDualOptimal C A b (slack C A y) y := by
  have hfeas : ∀ i, frob (A i) (R * Rᵀ) = b i := hstat.1
  have hpsd : (R * Rᵀ).PosSemidef := by
    have := posSemidef_self_mul_conjTranspose R
    simpa [conjTranspose_eq_transpose_of_trivial] using this
  have h0 := p9b_stat_zero C A b y R hstat
  have hval : frob C (R * Rᵀ) = b ⬝ᵥ y := by
    rw [p9b_frob_feas C A b y _ hfeas, h0, zero_add]
  refine ⟨⟨⟨hpsd, hfeas⟩, fun X' hX' => ?_⟩, ⟨⟨rfl, hS⟩, fun S' y' hS' => ?_⟩⟩
  · rw [hval, p9b_frob_feas C A b y X' hX'.2]
    linarith [p9b_frob_nonneg hS hX'.1]
  · obtain ⟨rfl, hS'psd⟩ := hS'
    have := p9b_frob_feas C A b y' _ hfeas
    rw [← hval, this]
    linarith [p9b_frob_nonneg hS'psd hpsd]
