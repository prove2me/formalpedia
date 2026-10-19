-- Prove2me | solution 1 for CauchyRiemannIndex.large_antilinear_perturbation_index
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-17T12:56:55.962664+00:00
-- url     : https://prove2.me/submissions/8b26b906-8894-4c03-a242-dbd0abaf4c36

import Theorems.Thm_CauchyRiemannIndex_large_antilinear_kernel_le
import Theorems.Thm_CauchyRiemannIndex_large_antilinear_cokernel_le
import Theorems.Thm_CauchyRiemannIndex_large_antilinear_kernel_ge
import Theorems.Thm_CauchyRiemannIndex_large_antilinear_cokernel_ge

open MeasureTheory Matrix Filter Topology CauchyRiemannIndex
open scoped ENNReal NNReal ContDiff RealInnerProductSpace

namespace LAP

theorem lap_aux (Splus Sminus : ℝ → Mat 1) (hSplus : IsSymLoop Splus)
    (hSminus : IsSymLoop Sminus) (hplus : IsNondegenerate Splus) (hminus : IsNondegenerate Sminus)
    (S : ℝ × ℝ → Mat 1) (hS : IsAsymptoticTo S Splus Sminus)
    (β : ℝ × ℝ → ℂ) (hβ : ContDiff ℝ ∞ β) (hβper : ∀ s t, β (s, t + 1) = β (s, t))
    (hβC1 : ∃ C : ℝ, ∀ x, ‖fderiv ℝ β x‖ ≤ C)
    (hβends : ∃ (R c : ℝ), 0 < c ∧ ∀ s t, R ≤ |s| → c ≤ ‖β (s, t)‖ ∧ ‖β (s, t)‖ ≤ 1 / c)
    (Zplus Zminus : Finset (ℝ × ℝ)) (hZ : ∀ ζ ∈ Zplus ∪ Zminus, 0 ≤ ζ.2 ∧ ζ.2 < 1)
    (hdisj : Disjoint Zplus Zminus)
    (hzero : ∀ x : ℝ × ℝ, β x = 0 ↔ ∃ ζ ∈ Zplus ∪ Zminus, ∃ m : ℤ, x = (ζ.1, ζ.2 + m))
    (r : ℝ) (hr : 0 < r)
    (hplusZ : ∀ ζ ∈ Zplus, ∀ z : ℂ, ‖z‖ < r →
      β (ζ.1 + z.re, ζ.2 + z.im) = z ∧ S (ζ.1 + z.re, ζ.2 + z.im) = 0)
    (hminusZ : ∀ ζ ∈ Zminus, ∀ z : ℂ, ‖z‖ < r →
      β (ζ.1 + z.re, ζ.2 + z.im) = (starRingEnd ℂ) z ∧ S (ζ.1 + z.re, ζ.2 + z.im) = 0) :
    (Zminus = ∅ → ∃ σ₀ : ℝ, ∀ σ ≥ σ₀,
      crRange 2 (fun x => S x + σ • antilinearMat (β x)) = ⊤ ∧
      FiniteDimensional ℝ (crKernel 2 (fun x => S x + σ • antilinearMat (β x))) ∧
      Module.finrank ℝ (crKernel 2 (fun x => S x + σ • antilinearMat (β x))) = Zplus.card) ∧
    (Zplus = ∅ → ∃ σ₀ : ℝ, ∀ σ ≥ σ₀,
      crKernel 2 (fun x => S x + σ • antilinearMat (β x)) = ⊥ ∧
      FiniteDimensional ℝ (LpCyl 1 2 ⧸ crRange 2 (fun x => S x + σ • antilinearMat (β x))) ∧
      Module.finrank ℝ (LpCyl 1 2 ⧸ crRange 2 (fun x => S x + σ • antilinearMat (β x))) =
        Zminus.card) := by
  obtain ⟨σ₁, h₁⟩ := large_antilinear_kernel_le Splus Sminus hSplus hSminus hplus hminus S hS β hβ hβper hβC1 hβends Zplus Zminus hZ hdisj hzero r hr hplusZ hminusZ
  obtain ⟨σ₂, h₂⟩ := large_antilinear_cokernel_le Splus Sminus hSplus hSminus hplus hminus S hS β hβ hβper hβC1 hβends Zplus Zminus hZ hdisj hzero r hr hplusZ hminusZ
  refine ⟨fun hZm => ?_, fun hZp => ?_⟩
  · obtain ⟨σ₃, h₃⟩ := large_antilinear_kernel_ge Splus Sminus hSplus hSminus hplus hminus S hS β hβ hβper hβC1 hβends Zplus Zminus hZ hdisj hzero r hr hplusZ hminusZ hZm
    refine ⟨max σ₁ (max σ₂ σ₃), fun σ hσ => ?_⟩
    have hσ₁ : σ ≥ σ₁ := le_trans (le_max_left _ _) hσ
    have hσ₂ : σ ≥ σ₂ := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hσ
    have hσ₃ : σ ≥ σ₃ := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hσ
    obtain ⟨hfin, hle⟩ := h₁ σ hσ₁
    obtain ⟨hcfin, hcle⟩ := h₂ σ hσ₂
    obtain ⟨v, hv⟩ := h₃ σ hσ₃
    have hge := hv.fintype_card_le_finrank
    rw [Fintype.card_fin] at hge
    rw [hZm, Finset.card_empty] at hcle
    refine ⟨?_, hfin, le_antisymm hle hge⟩
    have h0 : Module.finrank ℝ (LpCyl 1 2 ⧸ crRange 2 (fun x => S x + σ • antilinearMat (β x))) = 0 :=
      Nat.le_zero.mp hcle
    have := Module.finrank_zero_iff.mp h0
    exact Submodule.Quotient.subsingleton_iff.mp inferInstance
  · obtain ⟨σ₃, h₃⟩ := large_antilinear_cokernel_ge Splus Sminus hSplus hSminus hplus hminus S hS β hβ hβper hβC1 hβends Zplus Zminus hZ hdisj hzero r hr hplusZ hminusZ hZp
    refine ⟨max σ₁ (max σ₂ σ₃), fun σ hσ => ?_⟩
    have hσ₁ : σ ≥ σ₁ := le_trans (le_max_left _ _) hσ
    have hσ₂ : σ ≥ σ₂ := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hσ
    have hσ₃ : σ ≥ σ₃ := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hσ
    obtain ⟨hfin, hle⟩ := h₁ σ hσ₁
    obtain ⟨hcfin, hcle⟩ := h₂ σ hσ₂
    obtain ⟨v, hv⟩ := h₃ σ hσ₃
    have hge := hv.fintype_card_le_finrank
    rw [Fintype.card_fin] at hge
    rw [hZp, Finset.card_empty] at hle
    refine ⟨?_, hcfin, le_antisymm hcle hge⟩
    exact Submodule.finrank_eq_zero.mp (Nat.le_zero.mp hle)

end LAP

open CauchyRiemannIndex in
theorem solution (Splus Sminus : ℝ → Mat 1) (hSplus : IsSymLoop Splus)
    (hSminus : IsSymLoop Sminus) (hplus : IsNondegenerate Splus) (hminus : IsNondegenerate Sminus)
    (S : ℝ × ℝ → Mat 1) (hS : IsAsymptoticTo S Splus Sminus)
    (β : ℝ × ℝ → ℂ) (hβ : ContDiff ℝ ∞ β) (hβper : ∀ s t, β (s, t + 1) = β (s, t))
    (hβC1 : ∃ C : ℝ, ∀ x, ‖fderiv ℝ β x‖ ≤ C)
    (hβends : ∃ (R c : ℝ), 0 < c ∧ ∀ s t, R ≤ |s| → c ≤ ‖β (s, t)‖ ∧ ‖β (s, t)‖ ≤ 1 / c)
    (Zplus Zminus : Finset (ℝ × ℝ)) (hZ : ∀ ζ ∈ Zplus ∪ Zminus, 0 ≤ ζ.2 ∧ ζ.2 < 1)
    (hdisj : Disjoint Zplus Zminus)
    (hzero : ∀ x : ℝ × ℝ, β x = 0 ↔ ∃ ζ ∈ Zplus ∪ Zminus, ∃ m : ℤ, x = (ζ.1, ζ.2 + m))
    (r : ℝ) (hr : 0 < r)
    (hplusZ : ∀ ζ ∈ Zplus, ∀ z : ℂ, ‖z‖ < r →
      β (ζ.1 + z.re, ζ.2 + z.im) = z ∧ S (ζ.1 + z.re, ζ.2 + z.im) = 0)
    (hminusZ : ∀ ζ ∈ Zminus, ∀ z : ℂ, ‖z‖ < r →
      β (ζ.1 + z.re, ζ.2 + z.im) = (starRingEnd ℂ) z ∧ S (ζ.1 + z.re, ζ.2 + z.im) = 0) :
    (Zminus = ∅ → ∃ σ₀ : ℝ, ∀ σ ≥ σ₀,
      crRange 2 (fun x => S x + σ • antilinearMat (β x)) = ⊤ ∧
      FiniteDimensional ℝ (crKernel 2 (fun x => S x + σ • antilinearMat (β x))) ∧
      Module.finrank ℝ (crKernel 2 (fun x => S x + σ • antilinearMat (β x))) = Zplus.card) ∧
    (Zplus = ∅ → ∃ σ₀ : ℝ, ∀ σ ≥ σ₀,
      crKernel 2 (fun x => S x + σ • antilinearMat (β x)) = ⊥ ∧
      FiniteDimensional ℝ (LpCyl 1 2 ⧸ crRange 2 (fun x => S x + σ • antilinearMat (β x))) ∧
      Module.finrank ℝ (LpCyl 1 2 ⧸ crRange 2 (fun x => S x + σ • antilinearMat (β x))) =
        Zminus.card) :=
  LAP.lap_aux Splus Sminus hSplus hSminus hplus hminus S hS β hβ hβper hβC1 hβends Zplus Zminus hZ hdisj hzero r hr hplusZ hminusZ
