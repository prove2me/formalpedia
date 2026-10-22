-- Prove2me | solution 1 for FriezeKannan.CutDecomp.inductive_step
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T12:20:45.975624+00:00
-- url     : https://prove2.me/submissions/dd7e8aa8-4500-4b29-b5e2-c7070a32639e

import Mathlib
import Definitions.Def_FriezeKannan_CutDecomp_Setting

set_option autoImplicit false
open FriezeKannan.CutDecomp

theorem fk_drop {R C : Type*} [Fintype R] [Fintype C] [DecidableEq R] [DecidableEq C]
    (A W : Matrix R C ℝ) (ε : ℝ) (hε : 0 < ε) (S : Finset R) (T : Finset C)
    (h : ε * Real.sqrt ((S.card : ℝ) * T.card) * frobNorm A < |blockSum W S T|) :
    frobNorm (W - cutMatrix S T (blockSum W S T / ((S.card : ℝ) * T.card))) ^ 2
        - frobNorm W ^ 2 ≤ -ε ^ 2 * frobNorm A ^ 2 := by
  have hsq : ∀ M : Matrix R C ℝ, frobNorm M ^ 2 = ∑ i, ∑ j, M i j ^ 2 := by
    intro M
    unfold frobNorm
    exact Real.sq_sqrt (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _)
  have hF : 0 ≤ frobNorm A := Real.sqrt_nonneg _
  have hST : S.Nonempty ∧ T.Nonempty := by
    by_contra hcon
    have hB0 : blockSum W S T = 0 := by
      rcases not_and_or.mp hcon with h1 | h1
      · rw [Finset.not_nonempty_iff_eq_empty] at h1; simp [blockSum, h1]
      · rw [Finset.not_nonempty_iff_eq_empty] at h1; simp [blockSum, h1]
    rw [hB0, abs_zero] at h
    have : 0 ≤ ε * Real.sqrt ((S.card : ℝ) * T.card) * frobNorm A :=
      mul_nonneg (mul_nonneg hε.le (Real.sqrt_nonneg _)) hF
    linarith
  set B := blockSum W S T with hB
  set c : ℝ := (S.card : ℝ) * T.card with hc
  have hc0 : 0 ≤ c := by positivity
  have hcpos : 0 < c :=
    mul_pos (Nat.cast_pos.mpr (Finset.card_pos.mpr hST.1)) (Nat.cast_pos.mpr (Finset.card_pos.mpr hST.2))
  have hsum : ∑ i, ∑ j, ((W - cutMatrix S T (B / c)) i j ^ 2 - W i j ^ 2) =
      ∑ i ∈ S, ∑ j ∈ T, ((B / c) ^ 2 - 2 * (B / c) * W i j) := by
    have e1 : ∀ i j, ((W - cutMatrix S T (B / c)) i j ^ 2 - W i j ^ 2) =
        if i ∈ S then (if j ∈ T then ((B / c) ^ 2 - 2 * (B / c) * W i j) else 0) else 0 := by
      intro i j
      by_cases hi : i ∈ S <;> by_cases hj : j ∈ T <;>
        simp [cutMatrix, hi, hj, Matrix.sub_apply] <;> ring
    have e2 : ∀ i, ∑ j, (if i ∈ S then (if j ∈ T then ((B / c) ^ 2 - 2 * (B / c) * W i j) else 0) else 0)
        = if i ∈ S then ∑ j ∈ T, ((B / c) ^ 2 - 2 * (B / c) * W i j) else 0 := by
      intro i
      split_ifs
      · rw [Finset.sum_ite_mem, Finset.univ_inter]
      · simp
    simp_rw [e1, e2]
    rw [Finset.sum_ite_mem, Finset.univ_inter]
  have hval : ∑ i ∈ S, ∑ j ∈ T, ((B / c) ^ 2 - 2 * (B / c) * W i j) = - B ^ 2 / c := by
    have hWsum : ∑ i ∈ S, ∑ j ∈ T, W i j = B := rfl
    simp only [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum]
    rw [hWsum]
    have : (S.card : ℝ) * ((T.card : ℝ) * (B / c) ^ 2) = c * (B / c) ^ 2 := by rw [hc]; ring
    rw [this]
    field_simp
    ring
  have hdiff : frobNorm (W - cutMatrix S T (B / c)) ^ 2 - frobNorm W ^ 2 = - B ^ 2 / c := by
    rw [hsq, hsq, ← hval, ← hsum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [← Finset.sum_sub_distrib]
  rw [hdiff]
  have hX : 0 ≤ ε * Real.sqrt c * frobNorm A := mul_nonneg (mul_nonneg hε.le (Real.sqrt_nonneg _)) hF
  have h2 : (ε * Real.sqrt c * frobNorm A) ^ 2 < B ^ 2 := by
    have := pow_lt_pow_left₀ h hX (two_ne_zero)
    rwa [sq_abs] at this
  have h3 : (ε * Real.sqrt c * frobNorm A) ^ 2 = ε ^ 2 * c * frobNorm A ^ 2 := by
    rw [mul_pow, mul_pow, Real.sq_sqrt hc0]
  rw [h3] at h2
  have h5 : ε ^ 2 * frobNorm A ^ 2 ≤ B ^ 2 / c := by
    rw [le_div_iff₀ hcpos]; nlinarith [h2]
  have h6 : -B ^ 2 / c = -(B ^ 2 / c) := by ring
  linarith

theorem solution {R C : Type*} [Fintype R] [Fintype C] [DecidableEq R] [DecidableEq C]
    (A : Matrix R C ℝ) (ε : ℝ) (hε : 0 < ε) (t : ℕ)
    (Rs : Fin t → Finset R) (Cs : Fin t → Finset C) (d : Fin t → ℝ)
    (hinv : frobNorm (A - cutSum Rs Cs d) ^ 2 ≤ (1 - ε ^ 2 * t) * frobNorm A ^ 2) :
    (∀ (S : Finset R) (T : Finset C),
        |blockSum (A - cutSum Rs Cs d) S T|
          ≤ ε * Real.sqrt ((S.card : ℝ) * T.card) * frobNorm A) ∨
      ∃ (S : Finset R) (T : Finset C) (d' : ℝ),
        frobNorm (A - (cutSum Rs Cs d + cutMatrix S T d')) ^ 2
          ≤ (1 - ε ^ 2 * (t + 1)) * frobNorm A ^ 2 := by
  set W := A - cutSum Rs Cs d with hW
  by_cases hall : ∀ (S : Finset R) (T : Finset C),
      |blockSum W S T| ≤ ε * Real.sqrt ((S.card : ℝ) * T.card) * frobNorm A
  · exact Or.inl hall
  · right
    push_neg at hall
    obtain ⟨S, T, hST⟩ := hall
    refine ⟨S, T, blockSum W S T / ((S.card : ℝ) * T.card), ?_⟩
    have h1 := fk_drop A W ε hε S T hST
    rw [sub_add_eq_sub_sub, ← hW]
    push_cast
    nlinarith [h1, hinv]
