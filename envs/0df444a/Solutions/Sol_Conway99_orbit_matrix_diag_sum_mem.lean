-- Prove2me | solution 1 for Conway99.orbit_matrix_diag_sum_mem
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-09-07T13:20:16.771484+00:00
-- url     : https://prove2.me/submissions/10170cc5-120c-4682-9a51-20ace1f10790

import Mathlib

open Finset Matrix

namespace Wil

variable {C : Matrix (Fin 9) (Fin 9) ℕ}

/-- `B = C + 4·I - 2·J` as a real matrix. -/
noncomputable def B (C : Matrix (Fin 9) (Fin 9) ℕ) : Matrix (Fin 9) (Fin 9) ℝ :=
  Matrix.of fun i j => (C i j : ℝ) + 4 * (if i = j then 1 else 0) - 2

lemma B_apply (i j) : B C i j = (C i j : ℝ) + 4 * (if i = j then 1 else 0) - 2 := rfl

lemma B_herm (hs : ∀ i j, C i j = C j i) : (B C).IsHermitian := by
  ext i j
  simp only [Matrix.conjTranspose_apply, star_trivial, B_apply, hs j i]
  by_cases hij : i = j
  · subst hij; rfl
  · rw [if_neg hij, if_neg (Ne.symm hij)]

lemma B_mul (hs : ∀ i j, C i j = C j i) (hr : ∀ i, ∑ j, C i j = 14)
    (hq : ∀ i j, (∑ k, C i k * C k j) + C i j = (if i = j then 12 else 0) + 22) :
    B C * B C = (7 : ℝ) • B C := by
  have hrow : ∀ p : Fin 9, ∑ k, ((C p k : ℝ)) = 14 := by
    intro p
    have h : ((∑ k, C p k : ℕ) : ℝ) = ((14 : ℕ) : ℝ) := by rw [hr p]
    push_cast at h
    exact h
  have hcol : ∀ q : Fin 9, ∑ k, ((C k q : ℝ)) = 14 := by
    intro q
    have hswap : ∀ k : Fin 9, ((C k q : ℕ) : ℝ) = ((C q k : ℕ) : ℝ) := by
      intro k; rw [hs k q]
    simp only [hswap]
    exact hrow q
  ext i j
  have hsq : ∑ k, ((C i k : ℝ)) * ((C k j : ℝ))
      = (if i = j then (12 : ℝ) else 0) + 22 - (C i j : ℝ) := by
    have h : ((∑ k, C i k * C k j : ℕ) : ℝ) + ((C i j : ℕ) : ℝ)
        = (((if i = j then 12 else 0 : ℕ)) : ℝ) + ((22 : ℕ) : ℝ) := by
      rw [← Nat.cast_add, hq i j]; push_cast; ring
    push_cast at h
    by_cases hij : i = j
    · rw [if_pos hij] at h ⊢; linarith
    · rw [if_neg hij] at h ⊢; linarith
  simp only [Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul, B, Matrix.of_apply]
  have step : ∀ k : Fin 9,
      ((C i k : ℝ) + 4 * (if i = k then (1 : ℝ) else 0) - 2) *
        ((C k j : ℝ) + 4 * (if k = j then (1 : ℝ) else 0) - 2)
      = ((C i k : ℝ) * (C k j : ℝ))
        + (if i = k then 4 * (C k j : ℝ) else 0)
        + (if k = j then 4 * (C i k : ℝ) else 0)
        + (if i = k then (if k = j then (16 : ℝ) else 0) else 0)
        + (-2) * (C k j : ℝ) + (-2) * (C i k : ℝ)
        + (if k = j then (-8 : ℝ) else 0) + (if i = k then (-8 : ℝ) else 0)
        + 4 := by
    intro k
    split_ifs <;> ring
  rw [Finset.sum_congr rfl (fun k _ => step k)]
  simp only [Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ,
    if_true, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  rw [hsq, hrow i, hcol j]
  by_cases hij : i = j
  · simp only [if_pos hij]; ring
  · simp only [if_neg hij]; ring

/-- The trace of an orbit matrix is `10` or `24`. -/
theorem diag_sum_mem (hs : ∀ i j, C i j = C j i) (hr : ∀ i, ∑ j, C i j = 14)
    (hq : ∀ i j, (∑ k, C i k * C k j) + C i j = (if i = j then 12 else 0) + 22)
    (hd : ∀ i, C i i = 0 ∨ C i i = 2 ∨ C i i = 4) :
    (∑ i, C i i) = 10 ∨ (∑ i, C i i) = 24 := by
  classical
  have hBB := B_mul hs hr hq
  have hBh := B_herm hs
  set P : Matrix (Fin 9) (Fin 9) ℝ := (7 : ℝ)⁻¹ • B C with hPdef
  have hP2 : P * P = P := by
    rw [hPdef, Matrix.smul_mul, Matrix.mul_smul, hBB, smul_smul, smul_smul]
    norm_num
  have hPh : P.IsHermitian := by
    rw [hPdef]
    exact hBh.smul (by norm_num : star (7:ℝ)⁻¹ = (7:ℝ)⁻¹)
  -- eigenvalues of an idempotent are 0 or 1
  have hev : ∀ j, hPh.eigenvalues j = 0 ∨ hPh.eigenvalues j = 1 := by
    intro j
    have h1 : P *ᵥ (⇑(hPh.eigenvectorBasis j) : Fin 9 → ℝ)
        = hPh.eigenvalues j • (⇑(hPh.eigenvectorBasis j) : Fin 9 → ℝ) :=
      hPh.mulVec_eigenvectorBasis j
    have hne : (⇑(hPh.eigenvectorBasis j) : Fin 9 → ℝ) ≠ 0 :=
      (WithLp.ofLp_eq_zero 2).ne.2 (hPh.eigenvectorBasis.orthonormal.ne_zero j)
    obtain ⟨i0, hi0⟩ := Function.ne_iff.mp hne
    have h2 : (P * P) *ᵥ (⇑(hPh.eigenvectorBasis j) : Fin 9 → ℝ)
        = (hPh.eigenvalues j ^ 2) • (⇑(hPh.eigenvectorBasis j) : Fin 9 → ℝ) := by
      rw [← Matrix.mulVec_mulVec, h1, Matrix.mulVec_smul, h1, smul_smul]
      ring_nf
    rw [hP2, h1] at h2
    have h3 := congrFun h2 i0
    simp only [Pi.smul_apply, smul_eq_mul] at h3
    have h4 : hPh.eigenvalues j * (1 - hPh.eigenvalues j) = 0 := by
      have : hPh.eigenvalues j * (⇑(hPh.eigenvectorBasis j) : Fin 9 → ℝ) i0
          = hPh.eigenvalues j ^ 2 * (⇑(hPh.eigenvectorBasis j) : Fin 9 → ℝ) i0 := h3
      have h5 : (hPh.eigenvalues j - hPh.eigenvalues j ^ 2)
          * (⇑(hPh.eigenvectorBasis j) : Fin 9 → ℝ) i0 = 0 := by linarith [this]
      rcases mul_eq_zero.mp h5 with h | h
      · nlinarith [h]
      · exact absurd h hi0
    rcases mul_eq_zero.mp h4 with h | h
    · exact Or.inl h
    · exact Or.inr (by linarith)
  -- trace of P is the number of unit eigenvalues
  have htrP : P.trace = ∑ j, hPh.eigenvalues j := hPh.trace_eq_sum_eigenvalues
  have hcard : ∑ j, hPh.eigenvalues j
      = (((univ.filter (fun j => hPh.eigenvalues j = 1)).card : ℕ) : ℝ) := by
    rw [Finset.sum_congr rfl (fun j _ =>
      (by rcases hev j with h | h
          · rw [h, if_neg (by norm_num : ¬ (0:ℝ) = 1)]
          · rw [h, if_pos rfl] :
        hPh.eigenvalues j = if hPh.eigenvalues j = 1 then (1:ℝ) else 0))]
    rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const]
    simp
  have htrB : (B C).trace = ((∑ i, C i i : ℕ) : ℝ) + 18 := by
    have hdiag2 : ∀ x : Fin 9, B C x x = (C x x : ℝ) + 2 := by
      intro x; rw [B_apply, if_pos rfl]; ring
    rw [Matrix.trace]
    simp only [Matrix.diag_apply, hdiag2]
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    push_cast
    ring
  have htr2 : P.trace = (7:ℝ)⁻¹ * (((∑ i, C i i : ℕ) : ℝ) + 18) := by
    rw [hPdef, Matrix.trace_smul, htrB, smul_eq_mul]
  set a : ℕ := (univ.filter (fun j => hPh.eigenvalues j = 1)).card with hadef
  have hkey : ((∑ i, C i i : ℕ) : ℝ) + 18 = 7 * (a : ℝ) := by
    rw [htrP, hcard] at htr2
    field_simp at htr2
    linarith [htr2]
  have hkeyN : (∑ i, C i i) + 18 = 7 * a := by exact_mod_cast hkey
  have hale : a ≤ 9 := by
    rw [hadef]
    calc (univ.filter (fun j => hPh.eigenvalues j = 1)).card ≤ (univ : Finset (Fin 9)).card :=
          Finset.card_le_card (Finset.filter_subset _ _)
      _ = 9 := by simp
  have hle : (∑ i, C i i) ≤ 36 := by
    calc (∑ i, C i i) ≤ ∑ _i : Fin 9, 4 :=
          Finset.sum_le_sum (fun i _ => by rcases hd i with h | h | h <;> omega)
      _ = 36 := by simp
  have heven : 2 ∣ (∑ i, C i i) :=
    Finset.dvd_sum (fun i _ => by rcases hd i with h | h | h <;> omega)
  omega

end Wil

/-- **The trace of a Wilbrink orbit matrix is `10` or `24`.** -/
theorem solution
    (C : Matrix (Fin 9) (Fin 9) ℕ) (hsymm : ∀ i j, C i j = C j i)
    (hrow : ∀ i, ∑ j, C i j = 14)
    (hsq : ∀ i j, (∑ k, C i k * C k j) + C i j = (if i = j then 12 else 0) + 22)
    (hdiag : ∀ i, C i i = 0 ∨ C i i = 2 ∨ C i i = 4) :
    (∑ i, C i i) = 10 ∨ (∑ i, C i i) = 24 :=
  Wil.diag_sum_mem hsymm hrow hsq hdiag
