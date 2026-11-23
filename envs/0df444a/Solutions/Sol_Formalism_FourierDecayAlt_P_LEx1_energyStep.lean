-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.LEx1.energyStep
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:25:53.963889+00:00
-- url     : https://prove2.me/submissions/d651eefb-331b-4329-8f45-85e19c384ee3

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LemmaEprimeFromSteps
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StepClaimFromStepsFull
import Theorems.Thm_Formalism_FourierDecayAlt_P_LEx1_sum_Icc_one
import Theorems.Thm_Formalism_FourierDecayAlt_P_LEx1_th_nonneg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.LEx1
open Formalism.FourierDecayAlt.LE
open MeasureTheory Filter Topology Finset
open scoped ComplexConjugate
noncomputable section
namespace Formalism.FourierDecayAlt.P.LEx1
theorem _root_.solution : EnergyStep := by
  intro hTZ hGeom hTR B S c σ ε CR Cd CP h4 hε hCR hCd hCP hL hLbig hImp hInt hStar hT Y hY
  obtain ⟨hMeas, hWPos, hPReg, hI3, hAdjB, hJet, hI4, hI4', hI5a, hRes, hWR, hPR⟩ := hImp
  have hσ : (0:ℝ) ≤ σ := by linarith
  have hP : 0 < |S.P Y| := abs_pos.mpr (hPReg.2 Y hY)
  have hC7 : 0 ≤ C7 CR Cd CP := by unfold C7; positivity
  have hsq0 : ∀ ω, 0 ≤ LE.sq B S.dw S.X ω := fun ω =>
    Finset.sum_nonneg (fun a _ => mul_nonneg (hWPos.1 ω a).le (by positivity))
  have hAth : S.Ath ε σ ≤ S.A0 := by
    apply integral_mono_of_nonneg
    · exact Filter.Eventually.of_forall (fun ω => mul_nonneg (th_nonneg B ε σ hε ω) (hsq0 ω))
    · exact hInt
    · exact Filter.Eventually.of_forall (fun ω => by
        have := (hTR ε σ (B.G ω) hε hσ (B.G_pos ω)).2
        simpa using mul_le_mul_of_nonneg_right this (hsq0 ω))
  have hE0 : 0 ≤ S.Esup ε σ := by
    apply Real.sSup_nonneg
    rintro _ ⟨Y', hY', rfl⟩
    apply div_nonneg _ (abs_nonneg _)
    apply integral_nonneg
    intro ω
    exact mul_nonneg (th_nonneg B ε σ hε ω)
      (Finset.sum_nonneg (fun a _ => mul_nonneg (hWPos.2 Y' hY' ω a).le (by positivity)))
  set x := 8 * σ * ((S.r : ℝ) + 1) ^ 2 / S.L with hx
  have hx0 : 0 ≤ x := by rw [hx]; positivity
  have hden : 0 < 2 * (1 + 2 * Real.exp 1 * √(C7 CR Cd CP)) := by positivity
  have hx1 : x ≤ 1 / (2 * (1 + 2 * Real.exp 1 * √(C7 CR Cd CP))) := by
    rw [le_div_iff₀ hden, hx, div_mul_eq_mul_div, div_le_one hL]
    linarith
  have hG := hGeom (C7 CR Cd CP) x (S.r + 1) hC7 hx0 hx1
  rw [sum_Icc_one] at hG
  have hs := hStar ε hε Y hY
  rw [Finset.sum_range_succ', hTZ] at hs
  have hnorm : ‖∑ i ∈ range (S.r + 1), S.term ε σ Y (i + 1)‖ ≤ S.Esup ε σ * |S.P Y| / 2 := by
    calc _ ≤ ∑ i ∈ range (S.r + 1), ‖S.term ε σ Y (i + 1)‖ := norm_sum_le _ _
      _ ≤ ∑ i ∈ range (S.r + 1), (S.Esup ε σ * |S.P Y|) * (Real.exp 1 * √(C7 CR Cd CP) * x ^ (i + 1)) := by
          apply Finset.sum_le_sum
          intro i _
          have := hT Y hY (i + 1)
          calc _ ≤ _ := this
            _ = _ := by ring
      _ = (S.Esup ε σ * |S.P Y|) * ∑ i ∈ range (S.r + 1), (Real.exp 1 * √(C7 CR Cd CP) * x ^ (i + 1)) := by
          rw [Finset.mul_sum]
      _ ≤ (S.Esup ε σ * |S.P Y|) * (1 / 2) := mul_le_mul_of_nonneg_left hG (by positivity)
      _ = _ := by ring
  have hre : S.En ε σ Y = |S.P Y| * S.Ath ε σ - (∑ i ∈ range (S.r + 1), S.term ε σ Y (i + 1)).re := by
    have := congrArg Complex.re hs
    simp only [Complex.ofReal_re, Complex.add_re] at this
    linarith
  have hre2 : -(∑ i ∈ range (S.r + 1), S.term ε σ Y (i + 1)).re ≤ S.Esup ε σ * |S.P Y| / 2 := by
    have := Complex.abs_re_le_norm (∑ i ∈ range (S.r + 1), S.term ε σ Y (i + 1))
    have h2 := neg_abs_le (∑ i ∈ range (S.r + 1), S.term ε σ Y (i + 1)).re
    linarith
  rw [div_le_iff₀ hP]
  nlinarith
end Formalism.FourierDecayAlt.P.LEx1
