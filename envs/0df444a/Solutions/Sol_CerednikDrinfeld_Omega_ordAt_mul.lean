-- Prove2me | solution 1 for CerednikDrinfeld.Omega.ordAt_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/abb3ad20-92ff-52d7-a0a3-bebc8891a6ce

import Definitions.Def_CerednikDrinfeld_OmegaOrdAt
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Theorems.Thm_CerednikDrinfeld_Omega_coordSub_dvd_of_apply_eq_zero
import Theorems.Thm_CerednikDrinfeld_Omega_bddAbove_setOf_coordSub_pow_dvd
import Theorems.Thm_CerednikDrinfeld_Omega_isDomain_holRing
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_Omega_ordAt_mul

set_option autoImplicit false

p2m_open "CerednikDrinfeld.Omega P2MW.S_CerednikDrinfeld_Omega_ordAt_mul.CerednikDrinfeld.Omega"

namespace CerednikDrinfeld
p2m_export "CerednikDrinfeld" "Omega.coordSub_dvd_of_apply_eq_zero Omega.bddAbove_setOf_coordSub_pow_dvd Omega.isDomain_holRing"
namespace Omega
p2m_export "CerednikDrinfeld.Omega" "coordSub coordSub_apply coordSub_apply_self ordAt ordAt_def ordAt_le_of_forall_le le_ordAt_of_pow_dvd PseudoUniformizer IsExhausted holRing upperHalfPlane mem_upperHalfPlane_iff coordSub_dvd_of_apply_eq_zero bddAbove_setOf_coordSub_pow_dvd isDomain_holRing"
namespace OrdMulAsm
p2m_open "CerednikDrinfeld.Omega CerednikDrinfeld"

variable {K₀ : Type} [Field K₀] {K : Type} [Field K] [Algebra K₀ K]
variable {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]

theorem coe_mul_apply (ϖ : PseudoUniformizer K₀ K) (F G : ↥(holRing ϖ)) (w : ↥(upperHalfPlane K₀ K)) :
    ((F * G : ↥(holRing ϖ)) : ↥(upperHalfPlane K₀ K) → K) w =
      (F : ↥(upperHalfPlane K₀ K) → K) w * (G : ↥(upperHalfPlane K₀ K) → K) w := rfl

theorem apply_eq_zero_of_coordSub_dvd (ϖ : PseudoUniformizer K₀ K) (z : ↥(upperHalfPlane K₀ K)) {H : ↥(holRing ϖ)}
    (h : coordSub ϖ z ∣ H) : (H : ↥(upperHalfPlane K₀ K) → K) z = 0 := by
  obtain ⟨Q, rfl⟩ := h
  rw [coe_mul_apply, coordSub_apply_self, zero_mul]

theorem coordSub_ne_zero (ϖ : PseudoUniformizer K₀ K) (z : ↥(upperHalfPlane K₀ K)) : coordSub ϖ z ≠ 0 := by
  intro h
  have hz1 : (z : K) + 1 ∈ upperHalfPlane K₀ K := by
    rw [mem_upperHalfPlane_iff]
    intro x hx
    exact (mem_upperHalfPlane_iff K₀ (z : K)).1 z.2 (x - 1) (by rw [map_sub, map_one, hx, add_sub_cancel_right])
  have h1 : (coordSub ϖ z : ↥(upperHalfPlane K₀ K) → K) ⟨(z : K) + 1, hz1⟩ = 0 := by rw [h]; rfl
  rw [coordSub_apply, add_sub_cancel_left] at h1
  exact one_ne_zero h1

end CerednikDrinfeld.Omega.OrdMulAsm

open CerednikDrinfeld.Omega.OrdMulAsm in
theorem solution
    (K₀ : Type) [Field K₀] (K : Type) [Field K] [Algebra K₀ K]
    {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀] [CompleteSpace K] [IsAlgClosed K]
    (ϖ : PseudoUniformizer K₀ K)
    (hrk : ∀ x y : K, Valued.v x < 1 → y ≠ 0 → ∃ n : ℕ, Valued.v x ^ n ≤ Valued.v y)
    (hex : IsExhausted ϖ)
    (hfin : ∀ n : ℕ, ∃ T : Finset K₀, ∀ a : K₀,
      Valued.v (algebraMap K₀ K a) ≤ (Valued.v (algebraMap K₀ K ϖ.ϖ))⁻¹ ^ n →
        ∃ t ∈ T, Valued.v (algebraMap K₀ K a - algebraMap K₀ K t) < (Valued.v (algebraMap K₀ K ϖ.ϖ)) ^ n)
    (F G : ↥(holRing ϖ)) (hF : F ≠ 0) (hG : G ≠ 0) (z : ↥(upperHalfPlane K₀ K)) :
    ordAt ϖ (F * G) z = ordAt ϖ F z + ordAt ϖ G z := by
  classical
  haveI : IsDomain ↥(holRing ϖ) := CerednikDrinfeld.Omega.isDomain_holRing K₀ K ϖ hrk hex hfin
  set p : ↥(holRing ϖ) := coordSub ϖ z with hp
  have hp0 : p ≠ 0 := coordSub_ne_zero ϖ z
  have hdvd_iff : ∀ H : ↥(holRing ϖ), p ∣ H ↔ (H : ↥(upperHalfPlane K₀ K) → K) z = 0 := fun H =>
    ⟨apply_eq_zero_of_coordSub_dvd ϖ z,
     fun h0 => CerednikDrinfeld.Omega.coordSub_dvd_of_apply_eq_zero K₀ K ϖ hrk hex H z h0⟩
  have hprime : ∀ A B : ↥(holRing ϖ), p ∣ A * B → p ∣ A ∨ p ∣ B := fun A B h => by
    have h0 := (hdvd_iff _).1 h
    rw [coe_mul_apply, mul_eq_zero] at h0
    exact h0.imp (hdvd_iff A).2 (hdvd_iff B).2
  have hbdd : ∀ H : ↥(holRing ϖ), H ≠ 0 → BddAbove {n : ℕ | p ^ n ∣ H} := fun H hH =>
    CerednikDrinfeld.Omega.bddAbove_setOf_coordSub_pow_dvd K₀ K hrk ϖ hex hfin H hH z
  have hne : ∀ H : ↥(holRing ϖ), ({n : ℕ | p ^ n ∣ H} : Set ℕ).Nonempty := fun H => ⟨0, by simp⟩
  have hmax : ∀ H : ↥(holRing ϖ), H ≠ 0 → p ^ ordAt ϖ H z ∣ H ∧ ¬ p ^ (ordAt ϖ H z + 1) ∣ H := fun H hH => by
    refine ⟨?_, fun h => ?_⟩
    · have := Nat.sSup_mem (hne H) (hbdd H hH)
      rw [ordAt_def]; exact this
    · have := le_csSup (hbdd H hH) h
      rw [← ordAt_def] at this
      omega
  have hFG : F * G ≠ 0 := mul_ne_zero hF hG
  obtain ⟨a, ha⟩ : ∃ a : ℕ, ordAt ϖ F z = a := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b : ℕ, ordAt ϖ G z = b := ⟨_, rfl⟩
  have hFa := hmax F hF
  have hGb := hmax G hG
  rw [ha] at hFa
  rw [hb] at hGb
  rw [ha, hb]
  obtain ⟨F', hF'⟩ := hFa.1
  obtain ⟨G', hG'⟩ := hGb.1
  have hF'nd : ¬ p ∣ F' := fun h => hFa.2 (by
    obtain ⟨Q, hQ⟩ := h; exact ⟨Q, by rw [hF', hQ, pow_succ, mul_assoc]⟩)
  have hG'nd : ¬ p ∣ G' := fun h => hGb.2 (by
    obtain ⟨Q, hQ⟩ := h; exact ⟨Q, by rw [hG', hQ, pow_succ, mul_assoc]⟩)
  apply le_antisymm
  · apply ordAt_le_of_forall_le
    intro n hn
    by_contra hlt
    push_neg at hlt
    have hdiv : p ^ (a + b + 1) ∣ F * G :=
      (pow_dvd_pow p (by omega)).trans hn
    obtain ⟨Q, hQ⟩ := hdiv
    have hFGeq : F * G = p ^ (a + b) * (F' * G') := by
      rw [hF', hG', pow_add]; ring
    have hcancel : F' * G' = p * Q := by
      have h1 : p ^ (a + b) * (F' * G') = p ^ (a + b) * (p * Q) := by
        rw [← hFGeq, hQ, pow_succ, mul_assoc]
      exact mul_left_cancel₀ (pow_ne_zero _ hp0) h1
    rcases hprime F' G' ⟨Q, hcancel⟩ with h | h
    · exact hF'nd h
    · exact hG'nd h
  · apply le_ordAt_of_pow_dvd ϖ (F * G) z ?_ (hbdd _ hFG)
    exact ⟨F' * G', by rw [hF', hG', pow_add]; ring⟩

end S_CerednikDrinfeld_Omega_ordAt_mul
end P2MW
export P2MW.S_CerednikDrinfeld_Omega_ordAt_mul (solution)
