-- Prove2me | solution 1 for Formalism.CountingSumsFrames.ParamsIProof.sumP
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T16:21:14.39029+00:00
-- url     : https://prove2.me/submissions/587e2e6d-e691-451b-aa63-5d115fe895b6

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
theorem _root_.solution (k Y Yb Nr La L a b' : ℝ) (hk : 1 ≤ k) (hY : 1 ≤ Y) (hYb : 1 ≤ Yb) (hN : 1 ≤ Nr)
    (hLa : 0 ≤ La) (hL : 1 ≤ L) (hb : 0 < b') (ha0 : 0 < a)
    (ha : k * Y ^ 2 * Yb * Nr * La * L ≤ a / b')
    (hexp : Real.exp (-La / 3) ≤ 1 / a) (hYbNa : Yb * Nr ≤ a) :
    ∀ al : ℝ, a ≤ al →
      1 - 2 / (Yb * Nr) ≤ (1 - (k - 1) * (La * b' / k) / al) * (1 - Real.exp (-La / 3)) := by
  intro al hal
  have hk0 : 0 < k := by linarith
  have hY0 : 0 < Y := by linarith
  have hYb0 : 0 < Yb := by linarith
  have hN0 : 0 < Nr := by linarith
  have hal0 : 0 < al := by linarith
  have hA : k * Y ^ 2 * Yb * Nr * La * L * b' ≤ a := (le_div_iff₀ hb).mp ha
  have hJ0 : 0 ≤ La * b' / k := by positivity
  have hx0 : 0 ≤ (k - 1) * (La * b' / k) / al :=
    div_nonneg (mul_nonneg (by linarith) hJ0) hal0.le
  have hx : (k - 1) * (La * b' / k) / al ≤ 1 / (Yb * Nr) := by
    rw [div_le_div_iff₀ hal0 (by positivity)]
    have e0 : k * (La * b' / k) = La * b' := by field_simp
    have e1 : (k - 1) * (La * b' / k) ≤ La * b' := by linarith
    have e2 : (k - 1) * (La * b' / k) * (Yb * Nr) ≤ La * b' * (Yb * Nr) :=
      mul_le_mul_of_nonneg_right e1 (by positivity)
    have h1 : 1 ≤ k * Y ^ 2 * L :=
      one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hk (one_le_pow₀ hY)) hL
    have e3 : La * b' * (Yb * Nr) ≤ La * b' * (Yb * Nr) * (k * Y ^ 2 * L) :=
      le_mul_of_one_le_right (by positivity) h1
    linarith
  have hy0 : 0 ≤ Real.exp (-La / 3) := (Real.exp_pos _).le
  have hy : Real.exp (-La / 3) ≤ 1 / (Yb * Nr) :=
    le_trans hexp (one_div_le_one_div_of_le (by positivity) hYbNa)
  have e : 2 / (Yb * Nr) = 2 * (1 / (Yb * Nr)) := by ring
  nlinarith [mul_nonneg hx0 hy0]
end Formalism.CountingSumsFrames.ParamsIProof
