-- Prove2me | solution 1 for Formalism.CountingSumsFrames.ParamsIProof.share
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:44:00.477483+00:00
-- url     : https://prove2.me/submissions/86985a31-7c83-4826-933c-b04a8d6c8683

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
theorem _root_.solution (C k Y M a b' Ib Yb Nr La L : ℝ) (hC : 2 ≤ C) (hk : 2 ≤ k) (hY : 1 ≤ Y)
    (hM0 : 0 ≤ M) (hM : C * k ^ 3 * Y * M ≤ b') (hb : 0 < b') (hYb : 1 ≤ Yb) (hN : 1 ≤ Nr)
    (hLa : 1 ≤ La) (hL : 1 ≤ L) (ha : k * Y ^ 2 * Yb * Nr * La * L ≤ a / b')
    (hIb : Yb * Nr * La * b' / k ≤ Ib) : M * (k * Y / a + 1 / Ib) ≤ 1 / Y := by
  have hk0 : 0 < k := by linarith
  have hY0 : 0 < Y := by linarith
  have hC0 : 0 < C := by linarith
  have hA : k * Y ^ 2 * Yb * Nr * La * L * b' ≤ a := (le_div_iff₀ hb).mp ha
  have hR : 1 ≤ Y * Yb * Nr * La * L :=
    one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le
      (one_le_mul_of_one_le_of_one_le hY hYb) hN) hLa) hL
  have hR2 : 2 * Y ≤ k * Y ^ 2 * Yb * Nr * La * L := by
    have h1 : 2 * Y ≤ k * Y := by nlinarith
    have h2 : k * Y * 1 ≤ k * Y * (Y * Yb * Nr * La * L) :=
      mul_le_mul_of_nonneg_left hR (by nlinarith)
    linarith
  have ha0 : 0 < a := by nlinarith
  have hCk : 1 ≤ C * k ^ 2 := by nlinarith
  have p1 : M * (k * Y / a) ≤ 1 / (2 * Y) := by
    rw [show M * (k * Y / a) = M * k * Y / a by ring, div_le_div_iff₀ ha0 (by linarith)]
    have e1 : M * k * Y * (2 * Y) * 1 ≤ M * k * Y * (2 * Y) * (C * k ^ 2) :=
      mul_le_mul_of_nonneg_left hCk (by positivity)
    have e2 : C * k ^ 3 * Y * M * (2 * Y) ≤ b' * (2 * Y) := mul_le_mul_of_nonneg_right hM (by linarith)
    have e3 : b' * (2 * Y) ≤ b' * (k * Y ^ 2 * Yb * Nr * La * L) := mul_le_mul_of_nonneg_left hR2 hb.le
    linarith
  have hIb' : Yb * Nr * La * b' ≤ Ib * k := (div_le_iff₀ hk0).mp hIb
  have hYNL : 1 ≤ Yb * Nr * La :=
    one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hYb hN) hLa
  have e2 : b' ≤ Yb * Nr * La * b' := le_mul_of_one_le_left hb.le hYNL
  have hIb0 : 0 < Ib := by
    by_contra hneg
    rw [not_lt] at hneg
    nlinarith
  have p2 : M * (1 / Ib) ≤ 1 / (2 * Y) := by
    rw [show M * (1 / Ib) = M / Ib by ring, div_le_div_iff₀ hIb0 (by linarith)]
    have hCk3 : 0 < C * k ^ 3 := by positivity
    apply le_of_mul_le_mul_right _ hCk3
    have e1 : 2 * b' ≤ C * k ^ 2 * b' := mul_le_mul_of_nonneg_right (by nlinarith) hb.le
    have e3 : C * k ^ 2 * b' ≤ C * k ^ 2 * (Yb * Nr * La * b') := mul_le_mul_of_nonneg_left e2 (by positivity)
    have e4 : C * k ^ 2 * (Yb * Nr * La * b') ≤ C * k ^ 2 * (Ib * k) := mul_le_mul_of_nonneg_left hIb' (by positivity)
    linarith
  have e : 1 / (2 * Y) + 1 / (2 * Y) = 1 / Y := by field_simp; ring
  rw [mul_add]
  linarith
end Formalism.CountingSumsFrames.ParamsIProof
