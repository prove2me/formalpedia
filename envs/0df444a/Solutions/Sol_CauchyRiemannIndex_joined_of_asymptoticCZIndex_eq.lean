-- Prove2me | solution 1 for CauchyRiemannIndex.joined_of_asymptoticCZIndex_eq
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-16T12:53:33.184994+00:00
-- url     : https://prove2.me/submissions/86684d68-5fae-4270-8c57-6d1d2505eda8

import Definitions.Def_CauchyRiemannIndex_Setting
import Theorems.Thm_CauchyRiemannIndex_fundamentalSolution_existsUnique
import Theorems.Thm_CauchyRiemannIndex_fundamentalSolution_symplectic
import Theorems.Thm_CauchyRiemannIndex_asymptoticCZIndex_eq_czIndex
import Theorems.Thm_CauchyRiemannIndex_symplecticPath_family_of_czIndex_eq
import Theorems.Thm_CauchyRiemannIndex_joined_of_symplecticPath_family
import Mathlib.Analysis.Matrix.Normed

open CauchyRiemannIndex

theorem solution (n : ℕ) (S₀ S₁ : ℝ → Mat n) (h₀ : IsSymLoop S₀)
    (h₁ : IsSymLoop S₁) (hn₀ : IsNondegenerate S₀) (hn₁ : IsNondegenerate S₁)
    (h : asymptoticCZIndex S₀ = asymptoticCZIndex S₁) :
    ∃ H : C(unitInterval × ℝ, Mat n), (∀ t, H (0, t) = S₀ t) ∧ (∀ t, H (1, t) = S₁ t) ∧
      ∀ τ, IsSymLoop (fun t => H (τ, t)) ∧ IsNondegenerate (fun t => H (τ, t)) := by
  obtain ⟨Ψ₀, hΨ₀, -⟩ := fundamentalSolution_existsUnique n S₀ h₀.1
  obtain ⟨Ψ₁, hΨ₁, -⟩ := fundamentalSolution_existsUnique n S₁ h₁.1
  have hc₀ : Continuous Ψ₀ := continuous_iff_continuousAt.2 fun t => by
    letI : NormedAddCommGroup (Mat n) := Matrix.normedAddCommGroup
    letI : NormedSpace ℝ (Mat n) := Matrix.normedSpace
    exact (hΨ₀.2 t).continuousAt
  have hc₁ : Continuous Ψ₁ := continuous_iff_continuousAt.2 fun t => by
    letI : NormedAddCommGroup (Mat n) := Matrix.normedAddCommGroup
    letI : NormedSpace ℝ (Mat n) := Matrix.normedSpace
    exact (hΨ₁.2 t).continuousAt
  let ψ₀ : C(unitInterval, Mat n) := ⟨fun t => Ψ₀ t, hc₀.comp continuous_subtype_val⟩
  let ψ₁ : C(unitInterval, Mat n) := ⟨fun t => Ψ₁ t, hc₁.comp continuous_subtype_val⟩
  have e₀ := asymptoticCZIndex_eq_czIndex n S₀ h₀ hn₀ Ψ₀ hΨ₀ ψ₀ (fun _ => rfl)
  have e₁ := asymptoticCZIndex_eq_czIndex n S₁ h₁ hn₁ Ψ₁ hΨ₁ ψ₁ (fun _ => rfl)
  obtain ⟨G, hG₀, hG₁, hGs, hG0, hG1⟩ := symplecticPath_family_of_czIndex_eq n ψ₀ ψ₁
    (fun t => fundamentalSolution_symplectic n S₀ h₀.2.2 Ψ₀ hΨ₀ t)
    (by ext1; exact (show Ψ₀ 0 = 1 from hΨ₀.1) ▸ rfl) (by show (1 - Ψ₀ ((1 : unitInterval) : ℝ)).det ≠ 0; simpa using hn₀ Ψ₀ hΨ₀)
    (fun t => fundamentalSolution_symplectic n S₁ h₁.2.2 Ψ₁ hΨ₁ t)
    (by ext1; exact (show Ψ₁ 0 = 1 from hΨ₁.1) ▸ rfl) (by show (1 - Ψ₁ ((1 : unitInterval) : ℝ)).det ≠ 0; simpa using hn₁ Ψ₁ hΨ₁)
    (e₀ ▸ e₁ ▸ h)
  exact joined_of_symplecticPath_family n S₀ S₁ h₀ h₁ hn₀ hn₁ Ψ₀ Ψ₁ hΨ₀ hΨ₁ G hG₀ hG₁ hGs
    hG0 hG1
