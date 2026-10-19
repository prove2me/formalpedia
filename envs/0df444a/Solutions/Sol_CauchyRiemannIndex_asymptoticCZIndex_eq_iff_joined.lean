-- Prove2me | solution 1 for CauchyRiemannIndex.asymptoticCZIndex_eq_iff_joined
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-16T12:17:14.270178+00:00
-- url     : https://prove2.me/submissions/69ce8913-dc25-41da-8bee-6561b7d0e1b1

import Definitions.Def_CauchyRiemannIndex_Setting
import Theorems.Thm_CauchyRiemannIndex_asymptoticCZIndex_eq_of_joined
import Theorems.Thm_CauchyRiemannIndex_joined_of_asymptoticCZIndex_eq

open CauchyRiemannIndex in
theorem solution (n : ℕ) (S₀ S₁ : ℝ → Mat n) (h₀ : IsSymLoop S₀)
    (h₁ : IsSymLoop S₁) (hn₀ : IsNondegenerate S₀) (hn₁ : IsNondegenerate S₁) :
    asymptoticCZIndex S₀ = asymptoticCZIndex S₁ ↔
      ∃ H : C(unitInterval × ℝ, Mat n), (∀ t, H (0, t) = S₀ t) ∧ (∀ t, H (1, t) = S₁ t) ∧
        ∀ τ, IsSymLoop (fun t => H (τ, t)) ∧ IsNondegenerate (fun t => H (τ, t)) :=
  ⟨fun h => joined_of_asymptoticCZIndex_eq n S₀ S₁ h₀ h₁ hn₀ hn₁ h,
    fun ⟨H, hH₀, hH₁, hH⟩ => asymptoticCZIndex_eq_of_joined n S₀ S₁ H hH₀ hH₁ hH⟩
