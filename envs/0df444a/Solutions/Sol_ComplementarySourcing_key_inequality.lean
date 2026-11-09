-- Prove2me | solution 1 for ComplementarySourcing.key_inequality
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-08T09:11:54.110225+00:00
-- url     : https://prove2.me/submissions/fed04279-4e09-4f3d-994f-decaf1bfe81b

import Mathlib
import Definitions.Def_ComplementarySourcing_IsEffortCandidate1
import Definitions.Def_ComplementarySourcing_IsEffortCandidate2
import Definitions.Def_ComplementarySourcing_candidateProfit1
import Definitions.Def_ComplementarySourcing_candidateProfit2
import Definitions.Def_ComplementarySourcing_smallestMaxIndex
import Definitions.Def_ComplementarySourcing_riskLevel
import Definitions.Def_ComplementarySourcing_weightedRisk

namespace Aux_CompSourcing_key

open ComplementarySourcing

theorem gen {μ α r : ℝ} (hμ : 0 < μ) (hα : 0 ≤ α) (E W x : ℝ) (hx0 : 0 ≤ x) (hxE : x ≤ E)
    (hE : 0 < E) (hEW : E ≤ 2 * W) (hrW : 2 * E * W + E ^ 2 / 2 ≤ r * μ * W) :
    wholesaleCandidate μ α E x * μ * W
      < (r - wholesaleCandidate μ α E x) * μ * W - 1 / 2 * x ^ 2 := by
  have h1 : 1 ≤ (1 + α * x) ^ 2 := by nlinarith [mul_nonneg hα hx0]
  have heq : wholesaleCandidate μ α E x * μ = (E - x) / (1 + α * x) ^ 2 := by
    rw [wholesaleCandidate, div_mul_eq_mul_div, mul_comm (E - x) μ,
      mul_div_mul_left _ _ hμ.ne']
  have hw : wholesaleCandidate μ α E x * μ ≤ E - x := by
    rw [heq]
    exact div_le_self (sub_nonneg.mpr hxE) h1
  have hW : 0 < W := by linarith
  have a1 : wholesaleCandidate μ α E x * μ * W ≤ (E - x) * W :=
    mul_le_mul_of_nonneg_right hw hW.le
  have a2 : 0 ≤ x * (2 * E - x) := mul_nonneg hx0 (by linarith)
  have a3 : 0 ≤ x * (2 * W - E) := mul_nonneg hx0 (by linarith)
  have a4 : 0 < E ^ 2 := by positivity
  nlinarith

end Aux_CompSourcing_key

open ComplementarySourcing in
theorem solution {μ α r ε₀ σ x₁ x₂ π₁ π₂ xk wk : ℝ} {k : Fin 2}
    (hμ : 0 < μ) (hα : 0 ≤ α) (hσ₀ : 0 ≤ σ)
    (hx₁ : IsEffortCandidate1 α ε₀ σ x₁) (hx₂ : IsEffortCandidate2 α ε₀ σ x₂)
    (hπ₁ : π₁ = candidateProfit1 μ α r ε₀ σ x₁) (hπ₂ : π₂ = candidateProfit2 μ α r ε₀ σ x₂)
    (hk : k = smallestMaxIndex π₁ π₂) (hxk : xk = ![x₁, x₂] k)
    (hwk : wk = wholesaleCandidate μ α (riskLevel ε₀ σ k) xk)
    (hσ : σ < ε₀) (hr : r * μ ≥ 2 * (ε₀ + σ) + (ε₀ + σ) ^ 2 / (2 * (ε₀ - σ))) :
    wk * μ * weightedRisk ε₀ σ k < (r - wk) * μ * weightedRisk ε₀ σ k - 1 / 2 * xk ^ 2 := by
  have hd : 0 < ε₀ - σ := by linarith
  obtain ⟨q, hq⟩ : ∃ q, q = (ε₀ + σ) ^ 2 / (2 * (ε₀ - σ)) := ⟨_, rfl⟩
  rw [← hq] at hr
  have hq0 : 0 ≤ q := by rw [hq]; positivity
  have hq2 : q * (2 * (ε₀ - σ)) = (ε₀ + σ) ^ 2 := by
    rw [hq, div_mul_cancel₀ _ (by positivity)]
  have hk01 : k = 0 ∨ k = 1 := by fin_cases k <;> simp
  rcases hk01 with rfl | rfl
  · have hE : riskLevel ε₀ σ 0 = ε₀ + σ := rfl
    have hW : weightedRisk ε₀ σ 0 = 1 / 2 * (ε₀ + σ) + 1 / 2 * (ε₀ - σ) := rfl
    have hx : xk = x₁ := hxk
    rw [hwk, hE, hW, hx]
    obtain ⟨⟨h0, h1⟩, -⟩ := hx₁
    apply Aux_CompSourcing_key.gen hμ hα _ _ _ h0 h1 (by linarith) (by linarith)
    have hm := mul_le_mul_of_nonneg_right hr (show (0:ℝ) ≤ 1 / 2 * (ε₀ + σ) + 1 / 2 * (ε₀ - σ) by
      linarith)
    nlinarith [mul_nonneg hq0 hσ₀]
  · have hE : riskLevel ε₀ σ 1 = ε₀ - σ := rfl
    have hW : weightedRisk ε₀ σ 1 = (1 / 2 + 1 / 2) * (ε₀ - σ) := rfl
    have hx : xk = x₂ := hxk
    rw [hwk, hE, hW, hx]
    obtain ⟨⟨h0, h1⟩, -⟩ := hx₂
    apply Aux_CompSourcing_key.gen hμ hα _ _ _ h0 h1 hd (by linarith)
    have hsq : (ε₀ - σ) * (ε₀ - σ) ≤ q * (2 * (ε₀ - σ)) := by rw [hq2]; nlinarith
    have hqE : (ε₀ - σ) / 2 ≤ q := by nlinarith
    have hr2 : 2 * (ε₀ - σ) + (ε₀ - σ) / 2 ≤ r * μ := by linarith
    have hm := mul_le_mul_of_nonneg_right hr2 hd.le
    nlinarith
