-- Prove2me | solution 1 for FracPackCover.Covering.lemma_3_1
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T08:10:47.534136+00:00
-- url     : https://prove2.me/submissions/71ee28a7-cb38-4260-aa3d-9ad793698305

import Mathlib
import Definitions.Def_FracPackCover_Covering_Basic

set_option autoImplicit false
open FracPackCover.Covering

theorem solution {m n : ℕ} [NeZero m] (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (P : Set (Fin n → ℝ)) (hdata : IsCoveringData A b P)
    (ε : ℝ) (hε : 0 < ε) (hε3 : ε < 1 / 3)
    (x : Fin n → ℝ) (hx : x ∈ P) (y : Fin m → ℝ) (hy : ∀ i, 0 ≤ y i) (hy0 : y ≠ 0)
    (xt : Fin n → ℝ) (hxt : xt ∈ P) (hmax : ∀ x' ∈ P, yAx A y x' ≤ yAx A y xt)
    (hC1 : C1 A b ε (lam A b x) y x) (hC2 : C2 A b ε y x (yAx A y xt)) :
    (lam A b x ≤ 1 - 3 * ε → ¬ ∃ x' ∈ P, ∀ i, b i ≤ rowVal A x' i) ∧
    (1 - 3 * ε ≤ lam A b x → ∀ x' ∈ P, (1 - 3 * ε) * lam A b x' ≤ lam A b x) := by
  obtain ⟨hA, hb, hconv, hne, hnn⟩ := hdata
  have hytb : 0 < ytb b y := by
    obtain ⟨i, hi⟩ := Function.ne_iff.1 hy0
    have hi' : 0 < y i := lt_of_le_of_ne (hy i) (Ne.symm hi)
    unfold ytb
    apply Finset.sum_pos' (fun j _ => mul_nonneg (hy j) (hb j).le)
    exact ⟨i, Finset.mem_univ i, mul_pos hi' (hb i)⟩
  unfold C1 at hC1
  unfold C2 at hC2
  set C := yAx A y xt with hC
  set Y := yAx A y x with hY
  set T := ytb b y with hT
  constructor
  · intro hl ⟨x', hx', hxb⟩
    have h1 : T ≤ yAx A y x' := by
      unfold yAx
      rw [hT]; unfold ytb
      apply Finset.sum_le_sum
      intro i _
      exact mul_le_mul_of_nonneg_left (hxb i) (hy i)
    have h2 := hmax x' hx'
    have h3 : (1 + ε) * lam A b x * T ≤ (1 + ε) * (1 - 3 * ε) * T := by
      have : (1 + ε) * lam A b x ≤ (1 + ε) * (1 - 3 * ε) := by
        apply mul_le_mul_of_nonneg_left hl (by linarith)
      exact mul_le_mul_of_nonneg_right this hytb.le
    nlinarith [mul_pos hε hε, mul_pos (mul_pos hε hε) hytb]
  · intro hl x' hx'
    have hlb : ∀ i, lam A b x' * b i ≤ rowVal A x' i := by
      intro i
      have : lam A b x' ≤ rowVal A x' i / b i :=
        Finset.inf'_le (fun i => rowVal A x' i / b i) (Finset.mem_univ i)
      rwa [le_div_iff₀ (hb i)] at this
    have h1 : lam A b x' * T ≤ yAx A y x' := by
      unfold yAx
      rw [hT]; unfold ytb
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro i _
      have := mul_le_mul_of_nonneg_left (hlb i) (hy i)
      linarith
    have h2 := hmax x' hx'
    -- (1-ε) λ' T - ε T ≤ (1+ε) λ T
    have h4 : (1 - ε) * lam A b x' - ε ≤ (1 + ε) * lam A b x := by
      have h5 : ((1 - ε) * lam A b x' - ε) * T ≤ ((1 + ε) * lam A b x) * T := by
        nlinarith
      exact le_of_mul_le_mul_right h5 hytb
    have hlpos : 0 < 1 - 3 * ε := by linarith
    have hl0 : 0 ≤ lam A b x := by linarith
    have h6 : (1 - 3 * ε) * ((1 - ε) * lam A b x') ≤ (1 - 3 * ε) * ((1 + ε) * lam A b x + ε) := by
      apply mul_le_mul_of_nonneg_left (by linarith) hlpos.le
    have h7 : ε * (1 - 3 * ε) ≤ ε * lam A b x := mul_le_mul_of_nonneg_left hl hε.le
    have h8 : (1 - ε) * ((1 - 3 * ε) * lam A b x') ≤ (1 - ε) * lam A b x := by
      nlinarith [mul_nonneg hl0 (mul_pos hε hε).le]
    exact le_of_mul_le_mul_left h8 (by linarith)
