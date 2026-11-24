-- Prove2me | solution 1 for Formalism.IndefR.Fin.Four.IsSB.modul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:26:36.561925+00:00
-- url     : https://prove2.me/submissions/5e89f75d-fe6d-419a-b47d-a874826323bf

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
variable {L X : AddSubgroup W}
namespace Formalism.IndefR.Fin.Four
namespace IsSB
theorem _root_.solution {Y : AddSubgroup W} {χ : W → W → ℂ} (hχl : ∀ t t' y, χ (t + t') y = χ t y * χ t' y)
    (hχr : ∀ t y y', χ t (y + y') = χ t y * χ t y') (hχ0 : ∀ t y, χ t y ≠ 0)
    (hLL : ∀ x ∈ L ⊓ X, ∀ y ∈ L ⊓ Y, χ x y = 1) (hoY : ∀ y ∈ Y, ∃ k : ℕ, 0 < k ∧ k • y ∈ L)
    {Φ : W → ℂ} (h : IsSB L X Φ) {y : W} (hy : y ∈ Y) : IsSB L X (fun t => χ t y * Φ t) := by
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
  refine ⟨fun t ht => hs t (fun h0t => ht (by show χ t y * Φ t = 0; rw [h0t, mul_zero])),
    k * k3, Nat.mul_pos hk hk3, fun u hu t => ?_, fun t ht => ?_⟩
  · show χ (t + (k * k3) • u) y * Φ (t + (k * k3) • u) = χ t y * Φ t
    have hΦ : Φ (t + (k * k3) • u) = Φ t := by
      rw [← smul_smul]; exact hi _ ((L ⊓ X).nsmul_mem hu k3) t
    have hχu : χ ((k * k3) • u) y = 1 := by
      rw [hpow, mul_comm, pow_mul, ← hpow', hLL u hu (k3 • y) ⟨hy3, Y.nsmul_mem hy k3⟩, one_pow]
    rw [hΦ, hχl, hχu, mul_one]
  · have hΦt : Φ t ≠ 0 := fun h0t => ht (by show χ t y * Φ t = 0; rw [h0t, mul_zero])
    rw [mul_comm, ← smul_smul]
    exact L.nsmul_mem (hl t hΦt) k3
end IsSB
end Formalism.IndefR.Fin.Four
