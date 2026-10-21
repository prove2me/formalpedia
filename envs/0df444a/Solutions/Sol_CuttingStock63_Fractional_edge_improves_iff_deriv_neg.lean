-- Prove2me | solution 1 for CuttingStock63.Fractional.edge_improves_iff_deriv_neg
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T01:20:46.91489+00:00
-- url     : https://prove2.me/submissions/6f346712-8934-4e70-b9aa-82614d35e630

import Mathlib
import Definitions.Def_DermanSeqDecisions_LinProg_LinearFractional
set_option autoImplicit false
open DermanSeqDecisions.LinProg

theorem lin_line {n : ℕ} (c x v : Fin n → ℝ) (τ : ℝ) :
    ∑ i, c i * (x + τ • v) i = (∑ i, c i * x i) + τ * ∑ i, c i * v i := by
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem ratio_deriv_aux {n : ℕ} (c d x v : Fin n → ℝ) (hx : ∑ i, d i * x i ≠ 0) :
    HasDerivAt (fun τ : ℝ => fracObj c d (x + τ • v))
      (((∑ i, d i * x i) * (∑ i, c i * v i) - (∑ i, c i * x i) * (∑ i, d i * v i)) /
        (∑ i, d i * x i) ^ 2) 0 := by
  have hf : (fun τ : ℝ => fracObj c d (x + τ • v)) =
      fun τ : ℝ => ((∑ i, c i * x i) + τ * ∑ i, c i * v i) / ((∑ i, d i * x i) + τ * ∑ i, d i * v i) := by
    funext τ
    unfold fracObj
    rw [lin_line, lin_line]
  rw [hf]
  have h1 : HasDerivAt (fun τ : ℝ => (∑ i, c i * x i) + τ * ∑ i, c i * v i) (∑ i, c i * v i) 0 := by
    simpa using ((hasDerivAt_id (0:ℝ)).mul_const (∑ i, c i * v i)).const_add (∑ i, c i * x i)
  have h2 : HasDerivAt (fun τ : ℝ => (∑ i, d i * x i) + τ * ∑ i, d i * v i) (∑ i, d i * v i) 0 := by
    simpa using ((hasDerivAt_id (0:ℝ)).mul_const (∑ i, d i * v i)).const_add (∑ i, d i * x i)
  have h3 := h1.div h2 (by simpa using hx)
  refine h3.congr_deriv ?_
  simp only [zero_mul, add_zero]
  ring

theorem solution {n : ℕ} (c d x v : Fin n → ℝ) (T : ℝ) (hT : 0 < T)
    (hden : ∀ τ ∈ Set.Icc (0 : ℝ) T, ∑ i, d i * (x + τ • v) i ≠ 0) :
    (deriv (fun τ : ℝ => fracObj c d (x + τ • v)) 0 < 0 →
      ∀ τ ∈ Set.Ioc (0 : ℝ) T, fracObj c d (x + τ • v) < fracObj c d x) ∧
    (0 ≤ deriv (fun τ : ℝ => fracObj c d (x + τ • v)) 0 →
      ∀ τ ∈ Set.Icc (0 : ℝ) T, fracObj c d x ≤ fracObj c d (x + τ • v)) := by
  set z1 := ∑ i, c i * x i with hz1
  set z2 := ∑ i, d i * x i with hz2
  set a := ∑ i, c i * v i with ha
  set b := ∑ i, d i * v i with hb
  have hz2ne : z2 ≠ 0 := by
    have := hden 0 ⟨le_refl _, hT.le⟩
    simpa using this
  have hz2sq : 0 < z2 ^ 2 := by positivity
  have hDeq : ∀ τ : ℝ, ∑ i, d i * (x + τ • v) i = z2 + τ * b := fun τ => lin_line d x v τ
  have hpos : ∀ τ ∈ Set.Icc (0 : ℝ) T, 0 < (z2 + τ * b) * z2 := by
    intro τ hτ
    by_contra hneg
    push_neg at hneg
    have hne : z2 + τ * b ≠ 0 := by
      have := hden τ hτ
      rwa [hDeq] at this
    have hlt : (z2 + τ * b) * z2 < 0 := lt_of_le_of_ne hneg (mul_ne_zero hne hz2ne)
    have hbz : b * z2 < 0 := by
      by_contra hh
      push_neg at hh
      have : 0 ≤ τ * (b * z2) := mul_nonneg hτ.1 hh
      nlinarith
    have hs0 : 0 ≤ z2 ^ 2 / (-(b * z2)) := by
      apply div_nonneg hz2sq.le; linarith
    have hsτ : z2 ^ 2 / (-(b * z2)) ≤ τ := by
      rw [div_le_iff₀ (by linarith)]
      nlinarith
    have hzero : z2 + (z2 ^ 2 / (-(b * z2))) * b = 0 := by
      have hbz' : b * z2 ≠ 0 := hbz.ne
      have hb0 : b ≠ 0 := left_ne_zero_of_mul hbz'
      field_simp
      ring
    have := hden (z2 ^ 2 / (-(b * z2))) ⟨hs0, hsτ.trans hτ.2⟩
    rw [hDeq] at this
    exact this hzero
  have hderiv := (ratio_deriv_aux c d x v hz2ne).deriv
  rw [hderiv]
  have hdiff : ∀ τ ∈ Set.Icc (0 : ℝ) T, fracObj c d (x + τ • v) - fracObj c d x =
      τ * (z2 * a - z1 * b) / ((z2 + τ * b) * z2) := by
    intro τ hτ
    have hne : z2 + τ * b ≠ 0 := by
      have := hden τ hτ
      rwa [hDeq] at this
    unfold fracObj
    rw [lin_line, hDeq]
    rw [← hz1, ← hz2]
    field_simp
    ring
  constructor
  · intro hneg τ hτ
    have hτ' : τ ∈ Set.Icc (0 : ℝ) T := ⟨hτ.1.le, hτ.2⟩
    have h1 : z2 * a - z1 * b < 0 := by
      by_contra hh
      push_neg at hh
      have : 0 ≤ (z2 * a - z1 * b) / z2 ^ 2 := div_nonneg hh hz2sq.le
      linarith
    have := hdiff τ hτ'
    have h2 : τ * (z2 * a - z1 * b) / ((z2 + τ * b) * z2) < 0 :=
      div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg hτ.1 h1) (hpos τ hτ')
    linarith
  · intro hnn τ hτ
    have h1 : 0 ≤ z2 * a - z1 * b := by
      by_contra hh
      push_neg at hh
      have : (z2 * a - z1 * b) / z2 ^ 2 < 0 := div_neg_of_neg_of_pos hh hz2sq
      linarith
    have := hdiff τ hτ
    have h2 : 0 ≤ τ * (z2 * a - z1 * b) / ((z2 + τ * b) * z2) :=
      div_nonneg (mul_nonneg hτ.1 h1) (hpos τ hτ).le
    linarith
