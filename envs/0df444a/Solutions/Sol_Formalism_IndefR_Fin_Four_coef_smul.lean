-- Prove2me | solution 1 for Formalism.IndefR.Fin.Four.coef_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T09:43:20.609376+00:00
-- url     : https://prove2.me/submissions/9dd5a7fa-5077-47fd-a7bc-89e46c5fc3a4

import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_FinitePlaces_FourModel
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_FinitePlaces_FourExist

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option linter.style.haveILetI false
noncomputable section
open Formalism Formalism.IndefR Formalism.IndefR.Fin Formalism.IndefR.Fin.Four
variable {W V : Type*} [AddCommGroup W] [AddCommGroup V] [Module ℂ V]
variable {ρ : W → Module.End ℂ V} {χ : W → W → ℂ} {L X Y : AddSubgroup W} {f₀ : V}
  (hX : ∀ x ∈ X, ∀ x' ∈ X, ρ (x + x') = ρ x * ρ x')
  (hY : ∀ y ∈ Y, ∀ y' ∈ Y, ρ (y + y') = ρ y * ρ y')
  (hXY : ∀ x ∈ X, ∀ y ∈ Y, ρ x * ρ y = χ x y • (ρ y * ρ x))
  (hχl : ∀ t t' y, χ (t + t') y = χ t y * χ t' y)
  (hχr : ∀ t y y', χ t (y + y') = χ t y * χ t y') (hχ0 : ∀ t y, χ t y ≠ 0)
  (hLL : ∀ x ∈ L ⊓ X, ∀ y ∈ L ⊓ Y, χ x y = 1)
  (hdY : ∀ y ∈ Y, (∀ x ∈ L ⊓ X, χ x y = 1) → y ∈ L)
  (hfinX : ∀ k, 0 < k → Finite (Qt k (L ⊓ X))) (hfinY : ∀ k, 0 < k → Finite (Qt k (L ⊓ Y)))
  (htf : ∀ k : ℕ, 0 < k → ∀ t : W, k • t = 0 → t = 0)
  (hoX : ∀ x ∈ X, ∃ k : ℕ, 0 < k ∧ k • x ∈ L) (hoY : ∀ y ∈ Y, ∃ k : ℕ, 0 < k ∧ k • y ∈ L)
  (hfX : ∀ u ∈ L ⊓ X, ρ u f₀ = f₀) (hfY : ∀ u ∈ L ⊓ Y, ρ u f₀ = f₀)
include hfinX
namespace Formalism.IndefR.Fin.Four
theorem _root_.solution (Φ : W → ℂ) (c : ℂ) (a y : W) : coef χ L X (c • Φ) a y = c * coef χ L X Φ a y := by
  unfold coef
  obtain ⟨g, hg⟩ : ∃ g : W → ℂ, g = fun t => Φ (a + t) * (χ t y)⁻¹ := ⟨_, rfl⟩
  have hg' : (fun t => (c • Φ) (a + t) * (χ t y)⁻¹) = fun t => c * g t := by
    funext t; simp [hg, mul_assoc]
  rw [hg', ← hg]
  unfold integ
  by_cases hc : c = 0
  · subst hc
    simp only [zero_mul]
    split_ifs with h1
    · unfold avg; simp
    · rfl
  · have hiff : ∀ k, IsInv k (L ⊓ X) (fun t => c * g t) ↔ IsInv k (L ⊓ X) g := by
      intro k
      unfold IsInv
      constructor
      · intro h t ht u hu; exact mul_left_cancel₀ hc (h t ht u hu)
      · intro h t ht u hu; show c * g (t + k • u) = c * g t; rw [h t ht u hu]
    have hpred : (fun k => 0 < k ∧ IsInv k (L ⊓ X) (fun t => c * g t)) =
        (fun k => 0 < k ∧ IsInv k (L ⊓ X) g) :=
      funext fun k => propext (and_congr_right' (hiff k))
    have key : ∀ (p q : ℕ → Prop) (hp : ∃ k, p k) (hq : ∃ k, q k), p = q → hp.choose = hq.choose := by
      intro p q hp hq h; subst h; rfl
    by_cases hex : ∃ k, 0 < k ∧ IsInv k (L ⊓ X) g
    · have hex' : ∃ k, 0 < k ∧ IsInv k (L ⊓ X) (fun t => c * g t) := by rw [hpred]; exact hex
      rw [dif_pos hex', dif_pos hex, key _ _ hex' hex hpred]
      haveI := hfinX _ hex.choose_spec.1
      unfold avg
      rw [← mul_finsum _ c]
      ring
    · have hex' : ¬ ∃ k, 0 < k ∧ IsInv k (L ⊓ X) (fun t => c * g t) := by rw [hpred]; exact hex
      rw [dif_neg hex', dif_neg hex, mul_zero]
end Formalism.IndefR.Fin.Four
