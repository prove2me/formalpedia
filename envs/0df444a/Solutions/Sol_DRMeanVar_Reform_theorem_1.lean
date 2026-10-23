-- Prove2me | solution 1 for DRMeanVar.Reform.theorem_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-22T08:33:24.287909+00:00
-- url     : https://prove2.me/submissions/2b62c345-a2a7-47a8-b510-fa7d2a118004

import Mathlib
import Definitions.Def_DRMeanVar_Reform_Setting
import Theorems.Thm_DRMeanVar_Reform_proposition_1
import Theorems.Thm_DRMeanVar_Reform_proposition_3
import Theorems.Thm_DRMeanVar_Reform_thm1_proof_display_2

open MeasureTheory

namespace DRMeanVar.Reform

theorem empMean_neg_aux {d n : ℕ} (R : Fin n → (Fin d → ℝ)) (φ : Fin d → ℝ) :
    empMean R (-φ) = - empMean R φ := by
  unfold empMean
  simp [neg_dotProduct, Finset.sum_neg_distrib]

theorem pMean_neg_aux {d : ℕ} (P : Measure (Fin d → ℝ)) (φ : Fin d → ℝ) :
    pMean P (-φ) = - pMean P φ := by
  unfold pMean
  simp [neg_dotProduct, integral_neg]

theorem robustObj_eq_aux {d n : ℕ} [NeZero n]
    (R : Fin n → (Fin d → ℝ)) (q p : ENNReal) (δ αbar : ℝ)
    (hδ : 0 ≤ δ) (hq : 1 ≤ q) (hqtop : q ≠ ⊤)
    (hpq : p.HolderConjugate q) (φ : Fin d → ℝ) (hφ : φ ∈ F q δ αbar R) :
    robustObj q δ R φ = (dualObj p δ R φ : EReal) := by
  haveI : Fact (1 ≤ p) := ⟨hpq.one_le⟩
  obtain ⟨hmax, _, hat⟩ := thm1_proof_display_2 R q p δ αbar hδ hq hqtop hpq φ hφ
  have hN : 0 ≤ ‖WithLp.toLp p φ‖ := norm_nonneg _
  have hsδ := Real.sqrt_nonneg δ
  apply le_antisymm
  · unfold robustObj
    refine iSup₂_le fun P hP => ?_
    have h1 := (proposition_1 R q p δ hδ hq hqtop hpq φ).2 ⟨P, hP, rfl⟩
    have h2 := (proposition_1 R q p δ hδ hq hqtop hpq (-φ)).2 ⟨P, hP, rfl⟩
    simp only [empMean_neg_aux, pMean_neg_aux, WithLp.toLp_neg, norm_neg] at h1 h2
    set α := pMean P φ with hαdef
    have hfeas : (α - empMean R φ) ^ 2 - δ * ‖WithLp.toLp p φ‖ ^ 2 ≤ 0 := by
      have hsq : (Real.sqrt δ) ^ 2 = δ := Real.sq_sqrt hδ
      have : |α - empMean R φ| ≤ Real.sqrt δ * ‖WithLp.toLp p φ‖ := by
        rw [abs_le]; constructor <;> linarith
      have h3 : (α - empMean R φ) ^ 2 ≤ (Real.sqrt δ * ‖WithLp.toLp p φ‖) ^ 2 := by
        rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) this 2
      nlinarith
    have h3 := (proposition_3 R q p δ α hδ hq hqtop hpq φ hfeas).2 ⟨P, hP, rfl, rfl⟩
    have h4 := hmax.2 ⟨α, ⟨hφ.2 P hP, hfeas⟩, rfl⟩
    simp only at h4
    have : pVar P φ ≤ dualObj p δ R φ := by
      unfold pVar; rw [← hαdef]; linarith
    exact_mod_cast this
  · have hfeas0 : (empMean R φ - empMean R φ) ^ 2 - δ * ‖WithLp.toLp p φ‖ ^ 2 ≤ 0 := by
      simp; positivity
    obtain ⟨⟨P, hP, hPm, hPv⟩, _⟩ := proposition_3 R q p δ (empMean R φ) hδ hq hqtop hpq φ hfeas0
    unfold robustObj
    refine le_trans ?_ (le_iSup₂ (f := fun P (_ : P ∈ U q δ R) => (pVar P φ : EReal)) P hP)
    have : pVar P φ = dualObj p δ R φ := by
      unfold pVar; rw [hPm, ← hPv, hat]
    simp [this]

end DRMeanVar.Reform

open DRMeanVar.Reform in
theorem solution {d n : ℕ} [NeZero n]
    (R : Fin n → (Fin d → ℝ)) (q p : ENNReal) (δ αbar : ℝ)
    (hδ : 0 ≤ δ) (hq : 1 ≤ q) (hqtop : q ≠ ⊤)
    (hpq : p.HolderConjugate q) :
    (∀ φ : Fin d → ℝ,
      (φ ∈ F q δ αbar R ∧ IsMinOn (robustObj q δ R) (F q δ αbar R) φ) ↔
      (φ ∈ F q δ αbar R ∧
        IsMinOn (fun ψ => (dualObj p δ R ψ : EReal)) (F q δ αbar R) φ)) ∧
    (⨅ φ ∈ F q δ αbar R, robustObj q δ R φ) =
      (⨅ φ ∈ F q δ αbar R, (dualObj p δ R φ : EReal)) := by
  have key := fun φ hφ => robustObj_eq_aux R q p δ αbar hδ hq hqtop hpq φ hφ
  refine ⟨fun φ => ?_, ?_⟩
  · constructor
    · rintro ⟨hφ, hmin⟩
      refine ⟨hφ, isMinOn_iff.2 fun x hx => ?_⟩
      have := isMinOn_iff.1 hmin x hx
      rwa [key φ hφ, key x hx] at this
    · rintro ⟨hφ, hmin⟩
      refine ⟨hφ, isMinOn_iff.2 fun x hx => ?_⟩
      have := isMinOn_iff.1 hmin x hx
      rwa [key φ hφ, key x hx]
  · exact iInf_congr fun φ => iInf_congr fun hφ => key φ hφ
