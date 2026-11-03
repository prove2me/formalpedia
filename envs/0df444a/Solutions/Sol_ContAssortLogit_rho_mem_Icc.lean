-- Prove2me | solution 1 for ContAssortLogit.rho_mem_Icc
-- status  : ACCEPTED   (prove)
-- author  : @涼宮 ハルヒ
-- created : 2026-11-02T12:15:47.395376+00:00
-- url     : https://prove2.me/submissions/645063a4-4d59-4b66-856e-92b15a205568

import Definitions.Def_ContAssortLogit_Policy
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
open MeasureTheory Set ContAssortLogit
theorem solution (w : ℝ → ℝ) (hw : IsRevenueFn w) (α β ϱ₁ : ℝ) (hα : 0 < α)
    (hβ : max 0 (α - 1) ≤ β) (hϱ₁ : ϱ₁ ∈ Icc (0 : ℝ) 1) :
    ∀ (X : ℕ → PurchaseSpace) (n : ℕ), sapRho w α β ϱ₁ X n ∈ Icc (0 : ℝ) 1 := by
  classical
  have hwinv (r : ℝ) : winv w r ∈ Icc (0 : ℝ) 1 := by
    let S : Set ℝ := {x ∈ Icc (0 : ℝ) 1 | r ≤ w x} ∪ {1}
    have hlo : ∀ x ∈ S, (0 : ℝ) ≤ x := by
      intro x hx
      rcases hx with hx | hx
      · exact hx.1.1
      · have : x = 1 := hx
        subst x
        norm_num
    have hne : S.Nonempty := ⟨1, Or.inr (by simp)⟩
    have hb : BddBelow S := ⟨0, hlo⟩
    exact ⟨le_csInf hne hlo, csInf_le hb (Or.inr (by simp))⟩
  have hreward (r : ℝ) (X : PurchaseSpace) : sapReward w r X ∈ Icc (0 : ℝ) 1 := by
    cases X with
    | inl x =>
      change ((Icc (winv w r) 1).indicator w x) ∈ Icc (0 : ℝ) 1
      by_cases hx : x ∈ Icc (winv w r) 1
      · rw [indicator_of_mem hx]
        exact hw.1 ⟨(hwinv r).1.trans hx.1, hx.2⟩
      · rw [indicator_of_notMem hx]
        exact ⟨le_rfl, by norm_num⟩
    | inr x =>
      change (0 : ℝ) ∈ Icc (0 : ℝ) 1
      norm_num
  intro X n
  induction n with
  | zero => exact hϱ₁
  | succ n ih =>
    have hb0 : 0 ≤ β := (le_max_left _ _).trans hβ
    have hbα : α - 1 ≤ β := (le_max_right _ _).trans hβ
    have hden : 0 < (n + 1 : ℝ) + β := by positivity
    have ha0 : 0 ≤ α / ((n + 1 : ℝ) + β) := (div_pos hα hden).le
    have ha1 : α / ((n + 1 : ℝ) + β) ≤ 1 := by
      apply (div_le_one hden).mpr
      have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      linarith
    have hR := hreward (sapRho w α β ϱ₁ X n) (X n)
    rw [sapRho]
    constructor
    · nlinarith [mul_nonneg (sub_nonneg.mpr ha1) ih.1, mul_nonneg ha0 hR.1]
    · nlinarith [mul_nonneg (sub_nonneg.mpr ha1) (sub_nonneg.mpr ih.2),
        mul_nonneg ha0 (sub_nonneg.mpr hR.2)]
#print axioms solution
