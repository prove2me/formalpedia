-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.WirtingerIntegrationByParts.main_induction
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:36:40.081675+00:00
-- url     : https://prove2.me/submissions/36132c8e-bf5c-40aa-86eb-c80861fdbe5e

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WirtingerIntegrationByParts
import Theorems.Thm_Formalism_FourierDecayAlt_P_WirtingerIntegrationByParts_contDiff_smul_of_tsupport
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_WirtingerIntegrationByParts_tsupport_smul_subset__d2c1bc7b3def
import Theorems.Thm_Formalism_FourierDecayAlt_P_WirtingerIntegrationByParts_bk_contDiffOn
import Theorems.Thm_Formalism_FourierDecayAlt_P_WirtingerIntegrationByParts_wirt_contDiff
import Theorems.Thm_Formalism_FourierDecayAlt_P_WirtingerIntegrationByParts_wirt_tsupport
import Theorems.Thm_Formalism_FourierDecayAlt_P_WirtingerIntegrationByParts_wirt_bound
import Theorems.Thm_Formalism_FourierDecayAlt_P_WirtingerIntegrationByParts_base_bound
import Theorems.Thm_Formalism_FourierDecayAlt_P_WirtingerIntegrationByParts_fk_bound
import Theorems.Thm_Formalism_FourierDecayAlt_P_WirtingerIntegrationByParts_ibp_identity

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.WirtingerIntegrationByParts
open Formalism.FourierDecayAlt.G MeasureTheory
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V] {d : ℕ}
namespace Formalism.FourierDecayAlt.P.WirtingerIntegrationByParts
theorem _root_.solution {q : ℕ} {β t : ℂ} (hβ : β ≠ 0) (ht : t ≠ 0) {Ω : Set (Fin d → ℂ)} {g : (Fin d → ℂ) → ℂ}
    {η P B : ℝ} (hΩ : IsOpen Ω)
    (hg : DifferentiableOn ℂ g Ω) (hη : 0 < η) (hP : 0 < P) (hlow : ∀ x ∈ Ω, η ≤ ‖fderiv ℂ g x‖) (hB : 0 ≤ B)
    (hbk : ∀ x ∈ Ω, ∀ k, Bd (bk g k) Ω x q (B / ‖fderiv ℂ g x‖) P) :
    ∀ n ≤ q, ∀ (S : ℝ) (a : (Fin d → ℂ) → V), ContDiff ℝ n a → HasCompactSupport a → tsupport a ⊆ Ω →
      (∀ j ≤ n, ∀ x, ‖iteratedFDeriv ℝ j a x‖ ≤ S * P ^ j) →
      ‖∫ x : Fin d → ℂ, psi β (g x / t) • a x ∂(muPi β (Fin d))‖ ≤
        (2 / ‖β‖ * d * (2 ^ q * B)) ^ n * S * (‖t‖ * P / η) ^ n * (muPi β (Fin d) (tsupport a)).toReal := by
  have hne : ∀ x ∈ Ω, fderiv ℂ g x ≠ 0 := fun x hx h => by
    have := hlow x hx
    rw [h, norm_zero] at this
    linarith
  intro n
  induction n with
  | zero =>
    intro _ S a _ hc _ hb
    simp only [pow_zero, one_mul, mul_one]
    refine base_bound β t g hc fun x => ?_
    have := hb 0 le_rfl x
    simpa using this
  | succ n ih =>
    intro hn S a ha hc hsupp hb
    have hS : 0 ≤ S := by
      have := hb 0 (Nat.zero_le _) 0
      simp only [pow_zero, mul_one] at this
      exact (norm_nonneg _).trans this
    have hf : ∀ k, ContDiff ℝ (n + 1 : ℕ) (fun y => bk g k y • a y) := fun k =>
      contDiff_smul_of_tsupport hΩ (bk_contDiffOn hΩ hg hne k (n + 1)) ha hsupp
    have hfs : ∀ k, tsupport (fun y => bk g k y • a y) ⊆ tsupport a := fun k => tsupport_smul_subset' _ _
    have hws : ∀ k, tsupport (wirt k (fun y => bk g k y • a y)) ⊆ tsupport a := fun k =>
      (wirt_tsupport k _).trans (hfs k)
    have hfb := fun k => fk_bound hn hΩ hg hη hP hlow hB hbk ha hsupp hb k
    have hβ' : 0 < ‖β‖ := norm_pos_iff.mpr hβ
    have hk : ∀ k : Fin d, ‖∫ x : Fin d → ℂ, psi β (g x / t) • wirt k (fun y => bk g k y • a y) x
        ∂(muPi β (Fin d))‖ ≤ (2 / ‖β‖ * d * (2 ^ q * B)) ^ n * (2 ^ q * B * S / η * P) * (‖t‖ * P / η) ^ n *
          (muPi β (Fin d) (tsupport a)).toReal := by
      intro k
      have h1 := ih (Nat.le_of_succ_le hn) (2 ^ q * B * S / η * P) (wirt k (fun y => bk g k y • a y))
        (wirt_contDiff k (hf k)) (hc.of_isClosed_subset (isClosed_tsupport _) (hws k)) ((hws k).trans hsupp)
        (fun j hj x => by
          refine (wirt_bound k (hf k) hj x).trans ?_
          refine (hfb k (j + 1) (Nat.succ_le_succ hj) x).trans (le_of_eq ?_)
          ring)
      refine h1.trans ?_
      have h2 : (muPi β (Fin d) (tsupport (wirt k (fun y => bk g k y • a y)))).toReal ≤
          (muPi β (Fin d) (tsupport a)).toReal :=
        ENNReal.toReal_mono (IsCompact.measure_lt_top hc).ne (measure_mono (hws k))
      gcongr
    rw [ibp_identity hβ ht hΩ hg hne (ha.of_le (by norm_cast; omega)) hc hsupp]
    refine (norm_sum_le _ _).trans ?_
    have hc' : ‖-(2 * t / (Complex.I * β))‖ = 2 * ‖t‖ / ‖β‖ := by
      rw [norm_neg, norm_div, norm_mul, norm_mul, Complex.norm_I, one_mul]; simp
    calc ∑ k : Fin d, ‖(-(2 * t / (Complex.I * β))) • ∫ x : Fin d → ℂ, psi β (g x / t) •
            wirt k (fun y => bk g k y • a y) x ∂(muPi β (Fin d))‖
        ≤ ∑ _k : Fin d, (2 * ‖t‖ / ‖β‖) * ((2 / ‖β‖ * d * (2 ^ q * B)) ^ n * (2 ^ q * B * S / η * P) *
            (‖t‖ * P / η) ^ n * (muPi β (Fin d) (tsupport a)).toReal) := by
          refine Finset.sum_le_sum fun k _ => ?_
          rw [norm_smul, hc']
          gcongr
          exact hk k
      _ = _ := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          ring
end Formalism.FourierDecayAlt.P.WirtingerIntegrationByParts
