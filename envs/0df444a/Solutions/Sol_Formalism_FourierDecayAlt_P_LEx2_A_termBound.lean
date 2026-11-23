-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.LEx2.A.termBound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:29:14.115029+00:00
-- url     : https://prove2.me/submissions/05227d2e-b68f-44f2-a3fd-11c670d1cd45

import Definitions.Def_Formalism_HermitianCurvature_StatementLE
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ShiftBound
import Theorems.Thm_Formalism_FourierDecayAlt_P_LEx2_A_en_le_esup

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.LEx2 Formalism.FourierDecayAlt.P.LEx2.A
open Formalism.FourierDecayAlt.LE
open MeasureTheory Filter Topology Finset
open scoped ComplexConjugate
noncomputable section
namespace Formalism.FourierDecayAlt.P.LEx2.A
theorem _root_.solution : TermBound := by
  intro hCS hSh hMk hCI hEF hTB hCauchy hMarkovV B S c σ ε CR Cd CP h4 hε hCR hCd hCP hL hImp Y hY p
  obtain ⟨hMeas, hWPos, hPReg, hI3, hAdjB, hJet, hI4, hI4', hI5a, hRes, hWR, hPR⟩ := hImp
  have hσ : (0:ℝ) ≤ σ := by linarith
  have hb := hEF B S σ ε hε hPReg hI4'
  have hCoef : S.CoefInt σ := hCI B S σ hσ hMeas hWPos hI4 hI4'
  have h1 := hCS hTB hCauchy B S σ ε h4 hε hMeas hWPos hI4 hI4' hCoef Y hY p
  have h2 := hSh B S σ ε CR Cd CP hσ hε hCR hCd hCP hMeas hWPos hPReg hI4' hI5a hRes hWR hPR hb
  have h3 := hMk hMarkovV B S σ ε (C7 CR Cd CP * S.Esup ε σ * |S.P Y|) hσ hε hL hMeas hWPos hI4 hI4' Y hY
    (fun s hs => h2 Y s hY hs) p
  have h4' := en_le_esup S ε σ hb hPReg Y hY
  have hEn0 : 0 ≤ S.En ε σ Y := by
    apply integral_nonneg
    intro ω
    apply mul_nonneg
    · exact Real.rpow_nonneg (div_nonneg (B.G_pos ω).le (by have := B.G_pos ω; linarith)) _
    · exact Finset.sum_nonneg (fun a _ => mul_nonneg (hWPos.2 Y hY ω a).le (by positivity))
  set Q := S.Esup ε σ * |S.P Y| with hQ
  have hQ0 : 0 ≤ Q := le_trans hEn0 h4'
  have hC7 : 0 ≤ C7 CR Cd CP := by unfold C7; positivity
  set m := 2 * ((S.r : ℝ) + 1) ^ 2 / S.L with hm
  have hm0 : 0 ≤ m := by rw [hm]; positivity
  have e1 : √(S.En ε σ Y) ≤ √Q := Real.sqrt_le_sqrt h4'
  have e2 : √(S.Dn ε σ Y p) ≤ m ^ p * (√(C7 CR Cd CP) * √Q) := by
    have : S.Dn ε σ Y p ≤ (m ^ p) ^ 2 * (C7 CR Cd CP * Q) := by
      have e : (m ^ p) ^ 2 * (C7 CR Cd CP * Q) = m ^ (2 * p) * (C7 CR Cd CP * S.Esup ε σ * |S.P Y|) := by
        rw [hQ, ← pow_mul, mul_comm p 2]; ring
      rw [e]; exact h3
    calc √(S.Dn ε σ Y p) ≤ √((m ^ p) ^ 2 * (C7 CR Cd CP * Q)) := Real.sqrt_le_sqrt this
      _ = m ^ p * (√(C7 CR Cd CP) * √Q) := by
        rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity), Real.sqrt_mul hC7]
  have hpre : 0 ≤ Real.exp 1 * (4 * σ) ^ p := by positivity
  calc ‖S.term ε σ Y p‖ ≤ Real.exp 1 * (4 * σ) ^ p * √(S.En ε σ Y) * √(S.Dn ε σ Y p) := h1
    _ ≤ Real.exp 1 * (4 * σ) ^ p * √Q * (m ^ p * (√(C7 CR Cd CP) * √Q)) := by
        apply mul_le_mul (mul_le_mul_of_nonneg_left e1 hpre) e2 (Real.sqrt_nonneg _) (by positivity)
    _ = Real.exp 1 * √(C7 CR Cd CP) * (√Q * √Q) * ((4 * σ) * m) ^ p := by rw [mul_pow]; ring
    _ = Real.exp 1 * √(C7 CR Cd CP) * S.Esup ε σ * |S.P Y| * (8 * σ * ((S.r : ℝ) + 1) ^ 2 / S.L) ^ p := by
        rw [Real.mul_self_sqrt hQ0, hQ, hm]
        have : 4 * σ * (2 * ((S.r : ℝ) + 1) ^ 2 / S.L) = 8 * σ * ((S.r : ℝ) + 1) ^ 2 / S.L := by ring
        rw [this]; ring
end Formalism.FourierDecayAlt.P.LEx2.A
