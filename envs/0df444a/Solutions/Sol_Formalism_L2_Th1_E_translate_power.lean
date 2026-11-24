-- Prove2me | solution 1 for Formalism.L2.Th1.E.translate_power
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T11:12:48.680903+00:00
-- url     : https://prove2.me/submissions/657e6dc2-477d-4c33-bfc4-c0cd896f6fbd

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_TorsionTranslationPowers_StatementT
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_TorsionTranslationPowers_NonsingularJetNorms_ScaledXEqOffOrigin
import Theorems.Thm_Formalism_L2_Th1_E_Power_closed
import Theorems.Thm_Formalism_L2_Th1_E_Power_scaled_x_eq_off_origin

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
namespace Formalism.L2.Th1.E
theorem _root_.solution : TransPower := by
  intro K _ _ W T _ π G hG ε h0 t k hk
  obtain ⟨hG1, hG2, hG3⟩ := hG
  have hε : ε ≠ 0 := by
    obtain ⟨ε', hn, he⟩ := hG1 0 (map_zero π)
    have h1 : coeff 1 (C ε * X : K⟦X⟧) = coeff 1 (C ε' * X : K⟦X⟧) := by rw [← h0, ← he]
    simp only [coeff_C_mul, coeff_one_X, mul_one] at h1
    intro h
    rw [← h1, h, norm_zero] at hn
    exact zero_ne_one hn
  have hX : (X : K⟦X⟧) ≠ 0 := X_ne_zero
  have hne : ∀ j, j ≤ k → G (j • t) ≠ 0 := by
    intro j hj
    rcases Nat.eq_zero_or_pos j with rfl | hpos
    · rw [zero_smul, h0]
      exact mul_ne_zero (by simpa using hε) hX
    · intro h
      apply hG2 (j • t) (hk j hpos hj)
      rw [h, map_zero]
  have hrec : ∀ j, j + 1 ≤ k → G ((j + 2) • t) * G (j • t) =
      (C (constantCoeff (G t) ^ 2) * (C (px W (π t)) - xT W (π ((j + 1) • t)))) *
        G ((j + 1) • t) ^ 2 := by
    intro j hj
    have ht : π t ≠ 0 := by
      have := hk 1 le_rfl (by omega)
      rwa [one_smul] at this
    have h := hG3 ((j + 1) • t) t ht
    rw [Power.scaled_x_eq_off_origin W _ (hk (j + 1) (by omega) hj)] at h
    have e1 : (j + 1) • t + t = (j + 2) • t := by rw [← succ_nsmul]
    have e2 : (j + 1) • t - t = j • t := by rw [succ_nsmul]; abel
    rw [e1, e2] at h
    apply mul_left_cancel₀ (pow_ne_zero 2 hX)
    rw [h]; ring
  have h := Power.closed (fun j => G (j • t))
    (fun j => C (constantCoeff (G t) ^ 2) * (C (px W (π t)) - xT W (π (j • t)))) (C ε) X k
    (by simpa using h0) hne hrec k le_rfl
  simpa using h
end Formalism.L2.Th1.E
