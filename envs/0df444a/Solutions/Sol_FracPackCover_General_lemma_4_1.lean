-- Prove2me | solution 1 for FracPackCover.General.lemma_4_1
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T01:00:49.351523+00:00
-- url     : https://prove2.me/submissions/d45cde20-af0e-42f1-bb8b-9bfb9c38309f

import Mathlib
import Definitions.Def_FracPackCover_General_Basic

open FracPackCover.General

theorem solution {m n : ℕ} [NeZero m] (A : Matrix (Fin m) (Fin n) ℝ) (b d : Fin m → ℝ)
    (P : Set (Fin n → ℝ)) (hP : Convex ℝ P) (hd : ∀ i, 0 < d i)
    (x : Fin n → ℝ) (hx : x ∈ P) (y : Fin m → ℝ) (hy : 0 ≤ y) (hy0 : y ≠ 0)
    (xt : Fin n → ℝ) (hxt : xt ∈ P) (hmin : ∀ x' ∈ P, lagr A b y xt ≤ lagr A b y x')
    (hG1 : G1 A b d x (lam A b d x) y)
    (hG2 : G2 A b d x (lam A b d x) y (lagr A b y xt))
    (hlam : 0 < lam A b d x) :
    ¬ ∃ x' ∈ P, ∀ i, FracPackCover.Covering.rowVal A x' i ≤ b i := by
  classical
  have hp : 0 < ∑ i, y i * d i := by
    apply Finset.sum_pos'
    · intro i hi
      exact mul_nonneg (hy i) (hd i).le
    · have : ∃ i, y i ≠ 0 := by
        by_contra h
        apply hy0
        funext i
        simpa using (not_exists.mp h i)
      obtain ⟨i, hi⟩ := this
      exact ⟨i, Finset.mem_univ i, mul_pos (lt_of_le_of_ne (hy i) (Ne.symm hi)) (hd i)⟩
  intro ⟨z, hz, hf⟩
  have hn : lagr A b y z ≤ 0 := by
    unfold lagr
    apply Finset.sum_nonpos
    intro i hi
    exact mul_nonpos_of_nonneg_of_nonpos (hy i) (sub_nonpos.mpr (hf i))
  have hm := hmin z hz
  unfold G1 at hG1
  unfold G2 at hG2
  have := mul_pos hlam hp
  nlinarith

#print axioms solution
