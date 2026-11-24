-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.WirtingerIntegrationByParts.bk_bound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:25:22.77184+00:00
-- url     : https://prove2.me/submissions/9ae62c1c-6ced-4102-96c1-01c63bcc3527

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WirtingerIntegrationByParts
import Theorems.Thm_Formalism_FourierDecayAlt_P_WirtingerIntegrationByParts_Bd_smul
import Theorems.Thm_Formalism_FourierDecayAlt_P_WirtingerIntegrationByParts_Bd_sum
import Theorems.Thm_Formalism_FourierDecayAlt_P_WirtingerIntegrationByParts_Bd_clm
import Theorems.Thm_Formalism_FourierDecayAlt_P_WirtingerIntegrationByParts_Bd_inv
import Theorems.Thm_Formalism_FourierDecayAlt_P_WirtingerIntegrationByParts_bkb_Bd_mono
import Theorems.Thm_Formalism_FourierDecayAlt_P_WirtingerIntegrationByParts_bkb_sq_le
import Theorems.Thm_Formalism_FourierDecayAlt_P_WirtingerIntegrationByParts_bkb_N_pos
import Theorems.Thm_Formalism_FourierDecayAlt_P_WirtingerIntegrationByParts_bkb_u_contDiffOn
import Theorems.Thm_Formalism_FourierDecayAlt_P_WirtingerIntegrationByParts_bkb_cu_contDiffOn
import Theorems.Thm_Formalism_FourierDecayAlt_P_WirtingerIntegrationByParts_bkb_nsq_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_WirtingerIntegrationByParts_bkb_nsq_contDiffOn
import Theorems.Thm_Formalism_FourierDecayAlt_P_WirtingerIntegrationByParts_bkb_N_contDiffOn
import Theorems.Thm_Formalism_FourierDecayAlt_P_WirtingerIntegrationByParts_bkb_u_bd

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
namespace Formalism.FourierDecayAlt.P.WirtingerIntegrationByParts
theorem _root_.solution (d q : ℕ) : ∃ B : ℝ, 0 ≤ B ∧ ∀ (Ω : Set (Fin d → ℂ)) (g : (Fin d → ℂ) → ℂ) (P : ℝ), IsOpen Ω →
    DifferentiableOn ℂ g Ω → 0 < P → (∀ x ∈ Ω, fderiv ℂ g x ≠ 0) → ∀ x ∈ Ω,
    (∀ j : ℕ, 1 ≤ j → j ≤ q → ‖iteratedFDeriv ℂ (j + 1) g x‖ ≤ ‖fderiv ℂ g x‖ * P ^ j) →
    ∀ k : Fin d, Bd (bk g k) Ω x q (B / ‖fderiv ℂ g x‖) P := by
  refine ⟨2 ^ q * ((q.factorial : ℝ) ^ 2 * ((d : ℝ) ^ 2 * 2 ^ q) ^ q) * d, by positivity, ?_⟩
  intro Ω g P hΩ hg hP hne x hx hb k
  set G := ‖fderiv ℂ g x‖ with hG
  have hGpos : 0 < G := norm_pos_iff.mpr (hne x hx)
  have hd : 1 ≤ (d : ℝ) := by exact_mod_cast (Nat.succ_le_of_lt (Fin.pos k))
  have bu := fun l => bkb_u_bd hΩ hg hx hb l
  have bcu : ∀ l, Bd (fun x => (starRingEnd ℂ) (fderiv ℂ g x (Pi.single l 1))) Ω x q (1 * G) P := fun l =>
    Bd.clm (Complex.conjCLE : ℂ →L[ℝ] ℂ) hΩ hx hP.le ((bkb_u_contDiffOn hΩ hg l q).restrict_scalars ℝ)
      Complex.conjCLE_norm.le (bu l)
  have bn : ∀ l, Bd (fun x => Complex.normSq (fderiv ℂ g x (Pi.single l 1))) Ω x q
      (1 * (2 ^ q * (1 * G) * G)) P := fun l => by
    simp only [bkb_nsq_eq]
    exact Bd.clm Complex.reCLM hΩ hx hP.le
      ((bkb_cu_contDiffOn hΩ hg l q).smul ((bkb_u_contDiffOn hΩ hg l q).restrict_scalars ℝ))
      Complex.reCLM_norm.le
      (Bd.smul hΩ hx hP.le (bkb_cu_contDiffOn hΩ hg l q) ((bkb_u_contDiffOn hΩ hg l q).restrict_scalars ℝ)
        (bcu l) (bu l))
  have bN := Bd.sum (Finset.univ : Finset (Fin d)) hΩ hx (fun l _ => bkb_nsq_contDiffOn hΩ hg l q)
    (fun l _ => bn l)
  set N0 := ∑ l, Complex.normSq (fderiv ℂ g x (Pi.single l 1)) with hN0
  have hN0pos : 0 < N0 := bkb_N_pos (hne x hx)
  have hsq : G ^ 2 ≤ d * N0 := bkb_sq_le _
  have bN' : Bd (fun x => ∑ l, Complex.normSq (fderiv ℂ g x (Pi.single l 1))) Ω x q
      (((d : ℝ) ^ 2 * 2 ^ q) * N0) P := by
    refine bkb_Bd_mono hP.le ?_ bN
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, one_mul]
    have : (d : ℝ) * (2 ^ q * G * G) = d * 2 ^ q * G ^ 2 := by ring
    rw [this]
    calc (d : ℝ) * 2 ^ q * G ^ 2 ≤ d * 2 ^ q * (d * N0) := mul_le_mul_of_nonneg_left hsq (by positivity)
      _ = _ := by ring
  have hκ : (1 : ℝ) ≤ (d : ℝ) ^ 2 * 2 ^ q := by
    have h1 : (1 : ℝ) ≤ (d : ℝ) ^ 2 := one_le_pow₀ hd
    have h2 : (1 : ℝ) ≤ 2 ^ q := one_le_pow₀ (by norm_num)
    nlinarith
  have bI := Bd.inv hΩ hx hP.le (bkb_N_contDiffOn hΩ hg q) (fun y hy => (bkb_N_pos (hne y hy)).ne') hN0pos hκ bN'
  have bb := Bd.smul hΩ hx hP.le
    ((bkb_N_contDiffOn hΩ hg q).inv fun y hy => (bkb_N_pos (hne y hy)).ne') (bkb_cu_contDiffOn hΩ hg k q)
    bI (bcu k)
  refine bkb_Bd_mono hP.le ?_ bb
  rw [one_mul, le_div_iff₀ hGpos]
  set K := (q.factorial : ℝ) ^ 2 * ((d : ℝ) ^ 2 * 2 ^ q) ^ q with hK
  have hKnn : 0 ≤ K := by positivity
  have : 2 ^ q * (K / N0) * G * G = 2 ^ q * K * (G ^ 2 / N0) := by ring
  rw [this]
  have h3 : G ^ 2 / N0 ≤ d := by rw [div_le_iff₀ hN0pos]; exact hsq
  exact mul_le_mul_of_nonneg_left h3 (by positivity)
end Formalism.FourierDecayAlt.P.WirtingerIntegrationByParts
