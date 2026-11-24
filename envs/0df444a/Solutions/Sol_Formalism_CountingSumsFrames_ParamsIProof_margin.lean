-- Prove2me | solution 1 for Formalism.CountingSumsFrames.ParamsIProof.margin
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:51:08.134086+00:00
-- url     : https://prove2.me/submissions/87d74044-a413-4a29-a26d-53015d8f0acf

import Mathlib
import Definitions.Def_Formalism_PolynomialDimension_StatementNum
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_ParamsI

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.CountingSumsFrames
open Real
open Formalism.CountingSumsFrames.ParamsIProof
namespace Formalism.CountingSumsFrames.ParamsIProof
theorem _root_.solution (C Cm N1 k Q c La b' Ib X Nr Y : ℝ)
    (hCm : 1 ≤ Cm) (hC : 1000 * Cm ≤ C) (hN1 : 1 ≤ N1) (hk : 1 ≤ k) (hQ : 1 ≤ Q)
    (hLa : 1 ≤ La) (hIb : 0 ≤ Ib) (hb : 0 < b') (hc0 : 0 ≤ c) (hc : c ≤ 4 * X) (hX : 0 ≤ X)
    (hN : 1 ≤ Nr) (hY : 1 ≤ Y) (hb' : C * k ^ 3 * Nr * Q ^ 4 * X * Y ≤ b') :
    ∀ Ai : ℝ, b' / (2 * Q) ≤ Ai →
      2 * (Cm * k * N1 * Q * c) + 12 * c ≤ (C * N1 * La / k + 2 * Ib / b') * Ai / 4 := by
  intro Ai hAi
  have hQ0 : 0 < Q := by linarith
  have hk0 : 0 < k := by linarith
  have hC1 : 1 ≤ C := by linarith
  have hP : 1 ≤ Cm * k * N1 * Q :=
    one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le
      (one_le_mul_of_one_le_of_one_le hCm hk) hN1) hQ
  have h1 : 2 * (Cm * k * N1 * Q * c) + 12 * c ≤ 56 * Cm * k * N1 * Q * X := by
    nlinarith [mul_nonneg hc0 (sub_nonneg.mpr hP),
      mul_le_mul_of_nonneg_left hc (by linarith : (0:ℝ) ≤ Cm * k * N1 * Q)]
  have hq4 : Q ^ 2 ≤ Q ^ 4 := pow_le_pow_right₀ hQ (by norm_num)
  have hq : Q ^ 2 ≤ Nr * Q ^ 4 * Y := by
    have h2 : Q ^ 4 ≤ Nr * Q ^ 4 := le_mul_of_one_le_left (by positivity) hN
    have h3 : Nr * Q ^ 4 ≤ Nr * Q ^ 4 * Y := le_mul_of_one_le_right (by nlinarith) hY
    linarith
  have hCk3 : 0 ≤ C * k ^ 3 := mul_nonneg (by linarith) (by positivity)
  have hb2 : C * k ^ 3 * Q ^ 2 * X ≤ b' := by
    have h4 : C * k ^ 3 * Q ^ 2 * X ≤ C * k ^ 3 * (Nr * Q ^ 4 * Y) * X :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hq hCk3) hX
    linarith
  have hCLak : 1 ≤ C * La * k :=
    one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hC1 hLa) hk
  have hW : 0 ≤ N1 * k ^ 2 * Q ^ 2 * X := mul_nonneg (by positivity) hX
  have h2 : 56 * Cm * k * N1 * Q * X * (8 * k * Q) ≤ C * N1 * La * b' := by
    calc 56 * Cm * k * N1 * Q * X * (8 * k * Q) = 448 * Cm * (N1 * k ^ 2 * Q ^ 2 * X) := by ring
      _ ≤ C * (N1 * k ^ 2 * Q ^ 2 * X) := mul_le_mul_of_nonneg_right (by linarith) hW
      _ ≤ (C * La * k) * (C * (N1 * k ^ 2 * Q ^ 2 * X)) :=
          le_mul_of_one_le_left (mul_nonneg (by linarith) hW) hCLak
      _ = C * N1 * La * (C * k ^ 3 * Q ^ 2 * X) := by ring
      _ ≤ C * N1 * La * b' :=
          mul_le_mul_of_nonneg_left hb2 (mul_nonneg (mul_nonneg (by linarith) (by linarith)) (by linarith))
  have h3 : 56 * Cm * k * N1 * Q * X ≤ (C * N1 * La / k) * (b' / (2 * Q)) / 4 := by
    rw [show (C * N1 * La / k) * (b' / (2 * Q)) / 4 = (C * N1 * La * b') / (8 * k * Q) by
      field_simp; ring]
    rw [le_div_iff₀ (by positivity)]
    exact h2
  have hde0 : 0 ≤ C * N1 * La / k :=
    div_nonneg (mul_nonneg (mul_nonneg (by linarith) (by linarith)) (by linarith)) hk0.le
  have hde : C * N1 * La / k ≤ C * N1 * La / k + 2 * Ib / b' :=
    le_add_of_nonneg_right (div_nonneg (by linarith) hb.le)
  have hA0 : 0 ≤ b' / (2 * Q) := div_nonneg hb.le (by linarith)
  have h4 : (C * N1 * La / k) * (b' / (2 * Q)) ≤ (C * N1 * La / k + 2 * Ib / b') * Ai :=
    mul_le_mul hde hAi hA0 (by linarith)
  linarith
end Formalism.CountingSumsFrames.ParamsIProof
