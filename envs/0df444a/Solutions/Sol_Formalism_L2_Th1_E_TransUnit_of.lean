-- Prove2me | solution 1 for Formalism.L2.Th1.E.TransUnit_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T10:59:09.431232+00:00
-- url     : https://prove2.me/submissions/469f0143-a794-4d47-9c4c-b6dfec583b2f

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_TorsionTranslationPowers_StatementT
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_TorsionTranslationPowers_NonsingularJetNorms_ScaledXOffOrigin
import Theorems.Thm_Formalism_L2_Th1_E_Main_unitAt_one
import Theorems.Thm_Formalism_L2_Th1_E_Main_norm_natCast_of_dvd
import Theorems.Thm_Formalism_L2_Th1_E_Main_fac_exists
import Theorems.Thm_Formalism_ELL_FormalGroupPointsTorsion_key


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.E
open Main
namespace Formalism.L2.Th1.E
theorem _root_.solution (hR : IntRules) (hA : UnitAtRules) (hN : RootInt) (hF : FacShape)
    (hP : TransPower) : TransUnit := by
  intro K _ _ _ W hW T _ π G hI hG t N hNn hNt ht
  obtain ⟨-, -, -, -, -, -, -, -, oInv, -⟩ := hR K
  obtain ⟨uMul, uPow, -, -, -⟩ := hA K
  have hN0 : N ≠ 0 := by
    rintro rfl
    simp at hNn
  have hdvd : addOrderOf (π t) ∣ N := addOrderOf_dvd_of_nsmul_eq_zero hNt
  have hn0 : addOrderOf (π t) ≠ 0 := fun h => hN0 (by rw [h] at hdvd; exact Nat.eq_zero_of_zero_dvd hdvd)
  obtain ⟨k, hk⟩ : ∃ k, addOrderOf (π t) = k + 1 := Nat.exists_eq_succ_of_ne_zero hn0
  have hnn : ‖((k + 1 : ℕ) : K)‖ = 1 := hk ▸ norm_natCast_of_dvd hdvd hNn
  have hjk : ∀ j : ℕ, 1 ≤ j → j ≤ k → π (j • t) ≠ 0 := by
    intro j h1 h2 h
    rw [map_nsmul] at h
    have := Nat.le_of_dvd (by omega) (addOrderOf_dvd_of_nsmul_eq_zero h)
    omega
  have hkt : π ((k + 1) • t) = 0 := by
    rw [map_nsmul, ← hk, addOrderOf_nsmul_eq_zero]
  obtain ⟨ε, hε, hG0⟩ := hG.1 0 (map_zero π)
  obtain ⟨ε', hε', hGn⟩ := hG.1 _ hkt
  have key := hP K W T π G hG ε hG0 t k hjk
  have hc0 : constantCoeff (G t) ≠ 0 := hG.2.1 t ht
  generalize hc : constantCoeff (G t) = c at key hc0 ⊢
  have hprod : ∃ (r m : ℕ) (g : K⟦X⟧), UnitAt m g ∧
      ∏ j ∈ Finset.range k, (C (c ^ 2) * (C (px W (π t)) - xT W (π ((j + 1) • t)))) ^ (k - j) =
        C (c ^ r) * g := by
    apply Finset.prod_induction _
      (fun f => ∃ (r m : ℕ) (g : K⟦X⟧), UnitAt m g ∧ f = C (c ^ r) * g)
    · rintro _ _ ⟨r1, m1, g1, h1, rfl⟩ ⟨r2, m2, g2, h2, rfl⟩
      exact ⟨r1 + r2, m1 + m2, g1 * g2, uMul _ _ _ _ h1 h2, by rw [pow_add, map_mul]; ring⟩
    · exact ⟨0, 0, 1, unitAt_one, by simp⟩
    · intro j hj
      have hj' := Finset.mem_range.mp hj
      obtain ⟨e, he⟩ := fac_exists hF W hW π hI ((j + 1) • t) t (hjk (j + 1) (by omega) (by omega)) ht
      exact ⟨2 * (k - j), e * (k - j), _, uPow _ _ _ he, by rw [mul_pow, ← map_pow, ← pow_mul]⟩
  obtain ⟨r, m, g, ⟨a, V, ha, hV, rfl⟩, hpr⟩ := hprod
  rw [hpr, hGn] at key
  have ha0 : a ≠ 0 := by
    rintro rfl
    simp at ha
  have e1 : C (ε ^ k) * (C ε' * X) * X ^ k = C (ε ^ k * ε') * X ^ (k + 1) := by
    rw [map_mul]; ring
  have e2 : G t ^ (k + 1) * (C (c ^ r) * (C a * X ^ m * V)) =
      (G t ^ (k + 1) * C (c ^ r * a) * V) * X ^ m := by
    rw [map_mul]; ring
  rw [e1, e2] at key
  have hcm := congrArg (coeff m) key
  rw [coeff_C_mul, coeff_X_pow, coeff_mul_X_pow', if_pos le_rfl, Nat.sub_self,
    coeff_zero_eq_constantCoeff_apply, map_mul, map_mul, map_pow, hc, constantCoeff_C, hV.1,
    mul_one] at hcm
  have hne : c ^ (k + 1) * (c ^ r * a) ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ hc0) (mul_ne_zero (pow_ne_zero _ hc0) ha0)
  have hm : m = k + 1 := by
    by_contra hm
    rw [if_neg hm, mul_zero] at hcm
    exact hne hcm.symm
  subst hm
  rw [if_pos rfl, mul_one] at hcm
  have hcn : ‖c‖ = 1 := by
    have h1 := congrArg norm hcm
    rw [norm_mul, norm_mul, norm_mul, norm_pow, norm_pow, norm_pow, hε, hε', ha, one_pow, mul_one,
      mul_one, ← pow_add] at h1
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg c) (by omega)).mp h1.symm
  have key2 : C (ε ^ k * ε') = G t ^ (k + 1) * C (c ^ r * a) * V :=
    mul_right_cancel₀ (pow_ne_zero (k + 1) X_ne_zero) key
  have hinv : V * (C c⁻¹ * G t) ^ (k + 1) = 1 := by
    have hca : (C (c ^ r * a) : K⟦X⟧) ≠ 0 := by
      rw [Ne, map_eq_zero_iff _ C_injective]
      exact mul_ne_zero (pow_ne_zero _ hc0) ha0
    apply mul_left_cancel₀ hca
    calc C (c ^ r * a) * (V * (C c⁻¹ * G t) ^ (k + 1))
        = C (c⁻¹ ^ (k + 1)) * (G t ^ (k + 1) * C (c ^ r * a) * V) := by
          rw [mul_pow, map_pow]; ring
      _ = C (c⁻¹ ^ (k + 1) * (c ^ (k + 1) * (c ^ r * a))) := by
          rw [← key2, hcm, ← map_mul]
      _ = C (c ^ r * a) * 1 := by
          rw [mul_one, ← mul_assoc, ← mul_pow, inv_mul_cancel₀ hc0, one_pow, one_mul]
  have hone : constantCoeff (C c⁻¹ * G t) = 1 := by
    rw [map_mul, constantCoeff_C, hc, inv_mul_cancel₀ hc0]
  exact ⟨hcn, hone, hN K (k + 1) _ hnn hone (oInv _ _ hV hinv).2⟩
end Formalism.L2.Th1.E
