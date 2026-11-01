-- Prove2me | solution 1 for BankIntegration.Reversal.proposition_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T20:19:16.77005+00:00
-- url     : https://prove2.me/submissions/9aef4e76-a416-4809-9552-1d63706a340b

import Mathlib
import Definitions.Def_BankIntegration_Reversal_Model
import Theorems.Thm_BankIntegration_Reversal_lemma_1
import Theorems.Thm_BankIntegration_Reversal_lemma_2
import Theorems.Thm_BankIntegration_Reversal_eq_11
import Theorems.Thm_BankIntegration_Reversal_competitor_effect_neg
import Theorems.Thm_BankIntegration_Reversal_customer_effect_signs

open BankIntegration.Reversal in
theorem solution (lam a1 a2 b1 b2 : ℝ) (n : ℕ) (hS : Standing lam a1 a2 b1 b2 n)
    (hξ : xi a1 b1 < xi a2 b2)
    (L1 L2 : Fin n → ℝ) (LI : Fin (2 * n) → ℝ)
    (h1 : IsCournotEq lam 0 a1 b1 n L1) (h2 : IsCournotEq lam 0 a2 b2 n L2)
    (hI : IsCournotEq lam 0 (a1 + a2) (b1 + b2) (2 * n) LI) :
    let r1 := loanRate lam b1 (∑ i, L1 i)
    let r2 := loanRate lam b2 (∑ i, L2 i)
    let rS := loanRate lam (b1 + b2) (∑ i, LI i)
    let comp := bankCompetitorEffect lam n (xiStar a1 a2 b1 b2)
    let cust1 := bankCustomerEffect lam n (xi a1 b1) (xiStar a1 a2 b1 b2)
    (rS < r2 ∧
        ∀ θS θ2, IsOptimalRisk lam rS θS → IsOptimalRisk lam r2 θ2 → θS < θ2) ∧
      (cust1 < -comp → rS < r1 ∧
        ∀ θS θ1, IsOptimalRisk lam rS θS → IsOptimalRisk lam r1 θ1 → θS < θ1) ∧
      (-comp < cust1 → r1 < rS ∧
        ∀ θS θ1, IsOptimalRisk lam rS θS → IsOptimalRisk lam r1 θ1 → θ1 < θS) := by
  intro r1 r2 rS comp cust1
  have hS' := hS
  obtain ⟨hlam, ha1, ha2, hb1, hb2, hn⟩ := hS'
  obtain ⟨d1, d2⟩ := eq_11 lam a1 a2 b1 b2 n hS L1 L2 LI h1 h2 hI
  have hc := competitor_effect_neg lam a1 a2 b1 b2 n hS
  have hsg := customer_effect_signs lam a1 a2 b1 b2 n hS hξ
  have l1 := (lemma_1 lam a1 b1 n hlam ha1 hb1 hn).2 L1 h1
  have l2 := (lemma_1 lam a2 b2 n hlam ha2 hb2 hn).2 L2 h2
  have lI := (lemma_2 lam a1 a2 b1 b2 n hS).2.1 LI hI
  -- borrower-optimal risk is θ(r) = (λ + r)/2 at each equilibrium rate
  have t1 : ∀ θ, IsOptimalRisk lam r1 θ → θ = (lam + r1) / 2 := by
    intro θ h; have e := (l1.2.2.2 θ).mp h
    show θ = (lam + loanRate lam b1 (∑ i, L1 i)) / 2
    rw [e, l1.2.2.1]; ring
  have t2 : ∀ θ, IsOptimalRisk lam r2 θ → θ = (lam + r2) / 2 := by
    intro θ h; have e := (l2.2.2.2 θ).mp h
    show θ = (lam + loanRate lam b2 (∑ i, L2 i)) / 2
    rw [e, l2.2.2.1]; ring
  have tS : ∀ θ, IsOptimalRisk lam rS θ → θ = (lam + rS) / 2 := by
    intro θ h; have e := (lI.2.2.2 θ).mp h
    show θ = (lam + loanRate lam (b1 + b2) (∑ i, LI i)) / 2
    rw [e, lI.2.2.1]; ring
  have hr2 : rS < r2 := by
    have : rS - r2 < 0 := by
      show loanRate lam (b1 + b2) (∑ i, LI i) - loanRate lam b2 (∑ i, L2 i) < 0
      rw [d2]; linarith [hsg.2.2.1]
    linarith
  refine ⟨⟨hr2, fun θS θ2 hS2 h22 => ?_⟩, fun hw => ?_, fun hs => ?_⟩
  · rw [tS θS hS2, t2 θ2 h22]; linarith
  · have hr : rS < r1 := by
      have : rS - r1 < 0 := by
        show loanRate lam (b1 + b2) (∑ i, LI i) - loanRate lam b1 (∑ i, L1 i) < 0
        rw [d1]; linarith
      linarith
    exact ⟨hr, fun θS θ1 hS1 h11 => by rw [tS θS hS1, t1 θ1 h11]; linarith⟩
  · have hr : r1 < rS := by
      have : 0 < rS - r1 := by
        show 0 < loanRate lam (b1 + b2) (∑ i, LI i) - loanRate lam b1 (∑ i, L1 i)
        rw [d1]; linarith
      linarith
    exact ⟨hr, fun θS θ1 hS1 h11 => by rw [tS θS hS1, t1 θ1 h11]; linarith⟩
