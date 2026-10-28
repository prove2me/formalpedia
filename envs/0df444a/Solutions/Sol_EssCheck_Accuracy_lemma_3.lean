-- Prove2me | solution 1 for EssCheck.Accuracy.lemma_3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T03:21:49.254293+00:00
-- url     : https://prove2.me/submissions/de4e8e10-33b1-49d5-85e3-a4f9d72cb04a

import Mathlib
import Definitions.Def_EssCheck_Accuracy_Model

open EssCheck.Accuracy in
theorem solution {n : ℕ} (M : Model n) (hS : M.Standing)
    (hα : M.αbar = 1) (β : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1)
    (S : Finset (Fin n)) :
    socialWedge M S ≤ privateWedge M S β := by
  obtain ⟨hpH, hpL, hp0, hαpos, hα1, hl, hlv, -⟩ := hS
  have hlv' : ∀ i, M.l i < M.v i := fun i => by have := hlv i; rw [hα, one_mul] at this; exact this
  have hzt : ∀ i, 0 ≤ zt M i := by
    intro i
    unfold zt
    apply div_nonneg <;> linarith [hlv i, hl i]
  have h1 : ∑ i ∈ S, M.pH i * (M.v i - 2 * zt M i * M.l i *
      (M.αbar * M.v i / (M.αbar * M.v i - M.l i))) ≤
      ∑ i ∈ S, M.pH i * (M.αbar * M.v i - zt M i * M.l i) := by
    apply Finset.sum_le_sum
    intro i _
    apply mul_le_mul_of_nonneg_left _ (hpH.1 i)
    simp only [hα, one_mul]
    have hq : 1 ≤ M.v i / (M.v i - M.l i) := by
      rw [one_le_div (by linarith [hlv' i])]
      linarith [hl i]
    have hzl : 0 ≤ zt M i * M.l i := mul_nonneg (hzt i) (hl i).le
    nlinarith
  have h2 : ∑ i ∈ S, M.p0 i * M.l i ≤ ∑ i ∈ S, M.p0 i * M.v i :=
    Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hlv' i).le (hp0.1 i))
  have h3 : 0 ≤ ∑ i ∈ S, M.p0 i * M.l i :=
    Finset.sum_nonneg (fun i _ => mul_nonneg (hp0.1 i) (hl i).le)
  have h4 : 0 ≤ ∑ i ∈ Finset.univ \ S, M.p0 i * M.v i :=
    Finset.sum_nonneg (fun i _ => mul_nonneg (hp0.1 i) (by linarith [hlv' i, hl i]))
  have h5 : (1 - β) * ((∑ i ∈ S, M.p0 i * M.l i) + (∑ i ∈ Finset.univ \ S, M.p0 i * M.v i)) ≤
      (∑ i ∈ S, M.p0 i * M.l i) + (∑ i ∈ Finset.univ \ S, M.p0 i * M.v i) := by
    nlinarith
  unfold socialWedge privateWedge
  have e : ∑ i ∈ Finset.univ \ S, M.pH i * (M.αbar * M.v i) = ∑ i ∈ Finset.univ \ S, M.pH i * M.v i := by
    rw [hα]; simp only [one_mul]
  have e2 : ∑ i ∈ Finset.univ \ S, M.p0 i * (M.αbar * M.v i) = ∑ i ∈ Finset.univ \ S, M.p0 i * M.v i := by
    rw [hα]; simp only [one_mul]
  rw [e, e2]
  linarith
