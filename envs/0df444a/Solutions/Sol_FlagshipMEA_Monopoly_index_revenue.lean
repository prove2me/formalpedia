-- Prove2me | solution 1 for FlagshipMEA.Monopoly.index_revenue
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T03:12:46.804355+00:00
-- url     : https://prove2.me/submissions/d9129464-3cf6-4e07-8c09-2486bc24dc10

import Mathlib
import Definitions.Def_FlagshipMEA_Monopoly_Model

open FlagshipMEA.Monopoly in
theorem solution {n : ℕ} (D : Data n) (hS : D.Standing)
    (i : Fin n) (M : ℝ) (hM : 0 < M) :
    D.R i M = D.revenue (fun j => if j = i then M else 0) := by
  set E : Fin n → ℝ := fun j => Real.exp (D.u j / D.lam) with hE
  set W : ℝ := ∑ j, Real.exp ((D.u j + D.θ) / D.lam) with hW
  set S2 : ℝ := ∑ j, Real.exp ((D.u j + D.θ) / D.lam) * D.markup j with hS2
  have hattr : ∀ j, D.attraction (fun j => if j = i then M else 0) j =
      (if j = i then M * E i else 0) + Real.exp ((D.u j + D.θ) / D.lam) := by
    intro j
    unfold Data.attraction Data.base
    rw [add_div, Real.exp_add]
    by_cases h : j = i
    · subst h; simp [hE]; ring
    · simp [h]; ring
  have hsum : ∑ j, D.attraction (fun j => if j = i then M else 0) j = M * E i + W := by
    simp_rw [hattr]
    rw [Finset.sum_add_distrib, Finset.sum_ite_eq']
    simp [hW]
  have hmk : ∑ j, D.markup j * D.attraction (fun j => if j = i then M else 0) j =
      M * E i * D.markup i + S2 := by
    simp_rw [hattr, mul_add]
    rw [Finset.sum_add_distrib]
    congr 1
    · simp [mul_comm]
    · rw [hS2]; apply Finset.sum_congr rfl; intro j _; ring
  have hEi : 0 < E i := Real.exp_pos _
  have hW0 : 0 ≤ W := Finset.sum_nonneg (fun j _ => (Real.exp_pos _).le)
  unfold Data.revenue logitShare
  have : ∑ j, D.markup j * (D.attraction (fun j => if j = i then M else 0) j /
      (∑ k, D.attraction (fun j => if j = i then M else 0) k + 1)) =
      (∑ j, D.markup j * D.attraction (fun j => if j = i then M else 0) j) /
      (∑ k, D.attraction (fun j => if j = i then M else 0) k + 1) := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [this, hmk, hsum]
  unfold Data.R Data.A Data.B
  rw [← hW, ← hS2]
  have h1 : M * E i + W + 1 ≠ 0 := by positivity
  have h2 : Real.exp (D.u i / D.lam) + 1 / M * W + 1 / M ≠ 0 := by positivity
  simp only [hE] at h1 ⊢
  field_simp
  try ring
