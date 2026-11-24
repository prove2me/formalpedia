-- Prove2me | solution 1 for Formalism.IndefR.Fin.Four.coef_inv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:46:00.757981+00:00
-- url     : https://prove2.me/submissions/f59aba86-6c09-4070-8fff-74c77414b446

import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_FinitePlaces_FourModel
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_FinitePlaces_FourExist
import Theorems.Thm_Formalism_IndefR_Fin_Four_IsSB_trans

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
include hχl hχr hχ0 hLL hoY
namespace Formalism.IndefR.Fin.Four
theorem _root_.solution {Φ : W → ℂ} (h : IsSB L X Φ) (a : W) {y : W} (hy : y ∈ Y) :
    ∃ k, 0 < k ∧ IsInv k (L ⊓ X) (fun t => Φ (a + t) * (χ t y)⁻¹) := by
  obtain ⟨hs, k, hk, hi, hl⟩ := h
  obtain ⟨k3, hk3, hy3⟩ := hoY y hy
  have h0 : ∀ b, χ 0 b = 1 := by
    intro b
    have h1 := hχl 0 0 b
    rw [add_zero] at h1
    exact mul_left_cancel₀ (hχ0 0 b) (h1.symm.trans (mul_one _).symm)
  have h0' : ∀ a, χ a 0 = 1 := by
    intro a
    have h1 := hχr a 0 0
    rw [add_zero] at h1
    exact mul_left_cancel₀ (hχ0 a 0) (h1.symm.trans (mul_one _).symm)
  have hpow : ∀ (n : ℕ) (a b : W), χ (n • a) b = χ a b ^ n := by
    intro n a b
    induction n with
    | zero => rw [zero_smul, pow_zero, h0]
    | succ n ih => rw [succ_nsmul, hχl, ih, pow_succ]
  have hpow' : ∀ (n : ℕ) (a b : W), χ a (n • b) = χ a b ^ n := by
    intro n a b
    induction n with
    | zero => rw [zero_smul, pow_zero, h0']
    | succ n ih => rw [succ_nsmul, hχr, ih, pow_succ]
  refine ⟨k * k3, Nat.mul_pos hk hk3, fun t _ u hu => ?_⟩
  show Φ (a + (t + (k * k3) • u)) * (χ (t + (k * k3) • u) y)⁻¹ = Φ (a + t) * (χ t y)⁻¹
  have hΦ : Φ (a + t + (k * k3) • u) = Φ (a + t) := by
    rw [← smul_smul]; exact hi _ ((L ⊓ X).nsmul_mem hu k3) (a + t)
  have hχu : χ ((k * k3) • u) y = 1 := by
    rw [hpow, mul_comm, pow_mul, ← hpow', hLL u hu (k3 • y) ⟨hy3, Y.nsmul_mem hy k3⟩, one_pow]
  rw [← add_assoc, hΦ, hχl, hχu, mul_one]
end Formalism.IndefR.Fin.Four
