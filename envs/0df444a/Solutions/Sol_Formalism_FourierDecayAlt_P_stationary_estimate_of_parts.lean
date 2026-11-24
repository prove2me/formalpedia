-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.stationary_estimate_of_parts
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:05:39.481115+00:00
-- url     : https://prove2.me/submissions/91e7e8a2-eccc-448f-b85e-9d5bcdd51dd6

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StationaryPhaseEstimates
import Theorems.Thm_Formalism_FourierDecayAlt_P_DiagonalPointSigmaFinite_derivBound_mono
import Theorems.Thm_Formalism_FourierDecayAlt_P_DiagonalPointSigmaFinite_K_nonneg
import Theorems.Thm_Formalism_FourierDecayAlt_P_DiagonalPointSigmaFinite_continuous_critCut
import Theorems.Thm_Formalism_FourierDecayAlt_P_DiagonalPointSigmaFinite_critCut_mem_Icc
import Theorems.Thm_Formalism_FourierDecayAlt_P_DiagonalPointSigmaFinite_integrable_cut_smul
import Theorems.Thm_Formalism_FourierDecayAlt_P_DiagonalPointSigmaFinite_root_bound
import Theorems.Thm_Formalism_FourierDecayAlt_P_DiagonalPointSigmaFinite_root_ne_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_DiagonalPointSigmaFinite_inner_osc

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.DiagonalPointSigmaFinite
open Formalism.FourierDecayAlt.G Matrix MeasureTheory Filter Topology
noncomputable section
namespace Formalism.FourierDecayAlt.P.DiagonalPointSigmaFinite
namespace _root_.Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.G.StatStepOfParts := by
  intro hSP hG0D hG0C hHC hHD hNC hCC hABC hACC hMaj hOm hCut hIn
  obtain ⟨E₁, hE₁⟩ := hABC
  refine ⟨E₁ + 2, ?_⟩
  intro m β hβ Kc hKc h0 δ ε hδ hε hε2
  obtain ⟨Cst₁, t₁, ht₁, hA1⟩ := hE₁ m β Kc hKc h0 δ ε hδ hε hε2
  obtain ⟨t₂, ht₂, hA2⟩ := hACC m β Kc hKc h0 ε hε hε2
  obtain ⟨Rz, hRz1, hRz⟩ := root_bound (m := m) hKc
  obtain ⟨Λ, hΛ, hN⟩ := hNC m δ Rz hδ.1
  obtain ⟨C, hC⟩ := hSP (m + 1) β hβ (2 * δ) Λ (by linarith [hδ.1]) hΛ
  obtain ⟨CM, hCM⟩ := hMaj m (E₁ * (m + 2) ^ 2) β
  clear hE₁ hACC hNC hSP hMaj
  refine ⟨|C| * |Cst₁| * CM, min (min t₁ t₂) 1, lt_min (lt_min ht₁ ht₂) one_pos, ?_⟩
  intro V _ _ _ Φ A K k hA hk hΦ t c z ht htt hD hz
  have htt1 : ‖t‖ ≤ t₁ := htt.trans ((min_le_left _ _).trans (min_le_left _ _))
  have htt2 : ‖t‖ ≤ t₂ := htt.trans ((min_le_left _ _).trans (min_le_right _ _))
  have htt3 : ‖t‖ ≤ 1 := htt.trans (min_le_right _ _)
  have hK : 0 ≤ K := K_nonneg hD hΦ
  have hm : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  have hE : (0 : ℝ) ≤ (E₁ : ℝ) := Nat.cast_nonneg E₁
  push_cast at hA
  have hEm : 0 ≤ (E₁ : ℝ) * ((m : ℝ) + 2) ^ 2 := by positivity
  have hA0 : 0 ≤ A := by nlinarith
  have hAOm : ((m : ℝ) + 1) * ((m : ℝ) + 4) < A := by nlinarith
  have hAM : ((E₁ * (m + 2) ^ 2 : ℕ) : ℝ) + ((m : ℝ) + 2) * ((m : ℝ) + 1) + 1 ≤ A := by
    push_cast; nlinarith
  obtain ⟨hMi, hMb, -⟩ := hCM A hAM
  obtain ⟨-, -, hosc, -⟩ := inner_osc (β := β) hOm hCut hIn h0 hAOm hε.le hΦ ht htt3 hD
  generalize c * t ^ (m + 1) = D at *
  have hz0 : z ≠ 0 := root_ne_zero h0 hD hz
  have hD'0 : z ^ (m + 2) ≠ 0 := pow_ne_zero _ hz0
  obtain ⟨hN1, hN2, hN3⟩ := hN z (hδ.2 D hD z hz) (hRz D hD z hz)
  obtain ⟨hCC1, -, -⟩ := hCC m δ hδ.1
  have hF := integrable_cut_smul hosc (continuous_critCut δ z) (B := 1)
    (fun x => by rw [abs_of_nonneg (critCut_mem_Icc δ z x).1]; exact (critCut_mem_Icc δ z x).2)
  have hx₀ : ∀ k : Fin (m + 1), (fun _ : Fin (m + 1) => z) k ≠ 0 := fun _ => hz0
  have hcut1 : critCut δ z (fun _ : Fin (m + 1) => z) = 1 :=
    (hCC1 z _).2.2.1 (by rw [sub_self, norm_zero]; exact hδ.1.le)

  have hdet : ‖(Matrix.of (hess (z ^ (m + 2)) (fun _ : Fin (m + 1) => z)) :
      Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ).det‖ = ((m : ℝ) + 2) * (‖z‖ ^ (m + 1))⁻¹ := by
    rw [hHC m z hz0, hHD m z, norm_mul, norm_pow, norm_inv, inv_pow]
    congr 1
    have : ((m : ℂ) + 2) = (((m : ℝ) + 2 : ℝ) : ℂ) := by push_cast; ring
    rw [this, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
  have hconst : ‖t‖ ^ (m + 1) / ‖(Matrix.of (hess (z ^ (m + 2)) (fun _ : Fin (m + 1) => z)) :
      Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ).det‖ = ‖t‖ ^ (m + 1) * ‖z‖ ^ (m + 1) / ((m : ℝ) + 2) := by
    rw [hdet]
    have h1 : ‖z‖ ^ (m + 1) ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.mpr hz0)
    have h2 : (m : ℝ) + 2 ≠ 0 := by linarith
    field_simp

  have hpt : ∀ y : UT (m + 2) → ℂ,
      ‖∫ x : Fin (m + 1) → ℂ, ((critCut δ z x : ℝ) : ℂ) • oscIn β m ε Φ D t (x, y) ∂(muPi β (Fin (m + 1))) -
        (psi β (((m : ℂ) + 2) * z / t) * ((‖t‖ ^ (m + 1) * ‖z‖ ^ (m + 1) / ((m : ℝ) + 2) : ℝ) : ℂ)) •
          ampIn β m ε Φ D t (fun _ => z, y)‖ ≤
        C * (Cst₁ * K * (1 + ‖y‖) ^ (E₁ * (m + 2) ^ 2) * (max 1 ‖y‖) ^ (-A)) * ‖t‖ ^ (m + 1 + 1) := by
    intro y
    obtain ⟨ha1, ha2⟩ := hA1 V Φ A K k hA0 hk hΦ t D z ht htt1 hD hz y
    have := hC (fun _ => z) (g0 (z ^ (m + 2))) (dg0 (z ^ (m + 2)))
      (Matrix.of (hess (z ^ (m + 2)) (fun _ : Fin (m + 1) => z))) hN2 (fun x hx => (hN1 x hx).2)
      (fun x hx => (hG0D (m + 1) _ x (hN1 x hx).1).1)
      (((hG0C m _ hD'0).1 _ hx₀).2 ⟨z, rfl, rfl⟩)
      (fun i j => (hG0D (m + 1) _ _ hx₀).2 i j) hN3 V _ _ ha1
      (by
        intro x hx
        by_contra hx2
        rw [Metric.mem_closedBall, dist_eq_norm, not_le] at hx2
        apply hx
        show ((critCut δ z x : ℝ) : ℂ) • ampIn β m ε Φ D t (x, y) = 0
        rw [(hCC1 z x).2.2.2 hx2.le, Complex.ofReal_zero, zero_smul])
      ha2 t ht
    rw [hconst, (hG0C m _ hD'0).2 z rfl, hcut1, Complex.ofReal_one, one_smul] at this
    convert this using 5
    simp only [oscIn]
    rw [← hz, smul_comm]

  have hHint : Integrable (fun y : UT (m + 2) → ℂ => ampIn β m ε Φ D t (fun _ => z, y)) (muPi β (UT (m + 2))) := by
    have hcont := hA2 V Φ _ (derivBound_mono hΦ (Nat.zero_le k) subset_rfl) t D z ht htt2 hD hz
    refine (hMi.const_mul (Cst₁ * K)).mono' hcont.aestronglyMeasurable ?_
    refine Filter.Eventually.of_forall fun y => ?_
    have h1 := (hA1 V Φ A K k hA0 hk hΦ t D z ht htt1 hD hz y).2 0 (Nat.zero_le _) (fun _ => z)
    rw [norm_iteratedFDeriv_zero, hcut1, Complex.ofReal_one, one_smul] at h1
    calc _ ≤ _ := h1
      _ = _ := by ring
  have hGint : Integrable (fun y : UT (m + 2) → ℂ =>
      ∫ x : Fin (m + 1) → ℂ, ((critCut δ z x : ℝ) : ℂ) • oscIn β m ε Φ D t (x, y) ∂(muPi β (Fin (m + 1))))
      (muPi β (UT (m + 2))) := hF.integral_prod_right
  have hFub : ∫ p : XY m, ((critCut δ z p.1 : ℝ) : ℂ) • oscIn β m ε Φ D t p ∂(muXY β m) =
      ∫ y : UT (m + 2) → ℂ,
        ∫ x : Fin (m + 1) → ℂ, ((critCut δ z x : ℝ) : ℂ) • oscIn β m ε Φ D t (x, y) ∂(muPi β (Fin (m + 1)))
        ∂(muPi β (UT (m + 2))) := integral_prod_symm _ hF
  have hHs : Integrable (fun y : UT (m + 2) → ℂ =>
      (psi β (((m : ℂ) + 2) * z / t) * ((‖t‖ ^ (m + 1) * ‖z‖ ^ (m + 1) / ((m : ℝ) + 2) : ℝ) : ℂ)) •
        ampIn β m ε Φ D t (fun _ => z, y)) (muPi β (UT (m + 2))) := hHint.smul _
  rw [hFub, ← integral_smul, ← integral_sub hGint hHs]
  have hT : 0 ≤ ‖t‖ ^ (m + 2) := by positivity
  calc _ ≤ ∫ y : UT (m + 2) → ℂ, (|C| * |Cst₁| * K * ‖t‖ ^ (m + 2)) *
          ((1 + ‖y‖) ^ (E₁ * (m + 2) ^ 2) * (max 1 ‖y‖) ^ (-A)) ∂(muPi β (UT (m + 2))) := by
        refine norm_integral_le_of_norm_le (hMi.const_mul _) (Filter.Eventually.of_forall fun y => ?_)
        refine (hpt y).trans ?_
        have hp : 0 ≤ (1 + ‖y‖) ^ (E₁ * (m + 2) ^ 2) * (max 1 ‖y‖) ^ (-A) := by positivity
        have hcc : C * Cst₁ ≤ |C| * |Cst₁| := by rw [← abs_mul]; exact le_abs_self _
        calc C * (Cst₁ * K * (1 + ‖y‖) ^ (E₁ * (m + 2) ^ 2) * (max 1 ‖y‖) ^ (-A)) * ‖t‖ ^ (m + 1 + 1)
            = (C * Cst₁) * (K * ‖t‖ ^ (m + 2) * ((1 + ‖y‖) ^ (E₁ * (m + 2) ^ 2) * (max 1 ‖y‖) ^ (-A))) := by
              ring
          _ ≤ (|C| * |Cst₁|) * (K * ‖t‖ ^ (m + 2) * ((1 + ‖y‖) ^ (E₁ * (m + 2) ^ 2) * (max 1 ‖y‖) ^ (-A))) :=
              mul_le_mul_of_nonneg_right hcc (by positivity)
          _ = _ := by ring
    _ = (|C| * |Cst₁| * K * ‖t‖ ^ (m + 2)) *
          ∫ y : UT (m + 2) → ℂ, (1 + ‖y‖) ^ (E₁ * (m + 2) ^ 2) * (max 1 ‖y‖) ^ (-A) ∂(muPi β (UT (m + 2))) :=
        integral_const_mul _ _
    _ ≤ (|C| * |Cst₁| * K * ‖t‖ ^ (m + 2)) * CM := mul_le_mul_of_nonneg_left hMb (by positivity)
    _ = _ := by ring
end _root_.Formalism.FourierDecayAlt.P
end Formalism.FourierDecayAlt.P.DiagonalPointSigmaFinite
