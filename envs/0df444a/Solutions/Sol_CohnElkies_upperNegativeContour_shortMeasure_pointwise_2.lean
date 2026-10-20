-- Prove2me | solution 2 for CohnElkies.upperNegativeContour_shortMeasure_pointwise
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:32:40.694506+00:00
-- url     : https://prove2.me/submissions/46b74c9d-c0f1-4237-ac0e-87aa68f47323

import Mathlib
import Definitions.Def_SpherePacking
set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped Topology BigOperators


theorem solution
    {ε ℓ κ η a : ℝ}
    (hε : 0 < ε) (hεsmall : ε ≤ 1 / 4)
    (hℓ : 0 < ℓ) (hκ : 1 ≤ κ)
    (hη : 0 < η) (hκη : κ + η ≤ 3)
    (ha : 0 < a)
    (hmargin : 0 ≤ shortMargin ε a) :
    ℓ * (-shortShellDensity ε a) * Real.cosh (κ * a) ≤
      (1 - 4 * ε) * upperGammaMeasureDensity ℓ η a := by
  unfold shortShellDensity upperGammaMeasureDensity
  rw [neg_neg]
  have hca := Real.cosh_pos a
  have hm1 : shortMargin ε a ≤ 1 - 4 * ε := by unfold shortMargin; nlinarith
  have hcosh : Real.cosh (κ * a) / Real.cosh a ≤ Real.exp ((κ - 1) * a) := by
    rw [div_le_iff₀ hca]
    have hb : 0 ≤ (κ - 1) * a := mul_nonneg (by linarith) ha.le
    have hs : 0 ≤ Real.sinh ((κ - 1) * a) := Real.sinh_nonneg_iff.2 hb
    have hsc : Real.sinh a ≤ Real.cosh a := (Real.sinh_lt_cosh a).le
    rw [show κ * a = a + (κ - 1) * a by ring, Real.cosh_add, ← Real.cosh_add_sinh ((κ - 1) * a)]
    nlinarith [Real.cosh_pos ((κ - 1) * a)]
  have hX0 : 0 ≤ Real.cosh (κ * a) / Real.cosh a := div_nonneg (Real.cosh_pos _).le hca.le
  have hexp : Real.exp (-2 * a) * Real.exp ((κ - 1) * a) ≤ Real.exp (-η * a) := by
    rw [← Real.exp_add]; apply Real.exp_le_exp.2; nlinarith
  have hEX : Real.exp (-2 * a) * (Real.cosh (κ * a) / Real.cosh a) ≤ Real.exp (-η * a) :=
    le_trans (mul_le_mul_of_nonneg_left hcosh (Real.exp_pos _).le) hexp
  have hD1 : 1 - 2 * a / ℓ ≤ Real.exp (-(2 * a / ℓ)) := by linarith [Real.add_one_le_exp (-(2 * a / ℓ))]
  have hD0 : 0 < 1 - Real.exp (-(2 * a / ℓ)) := by
    have : Real.exp (-(2 * a / ℓ)) < 1 := Real.exp_lt_one_iff.mpr (by have := div_pos (by linarith : (0:ℝ) < 2 * a) hℓ; linarith)
    linarith
  have eqL : ℓ * (shortMargin ε a * Real.exp (-2 * a) / (2 * a ^ 2 * Real.cosh a)) * Real.cosh (κ * a)
      = ℓ * shortMargin ε a / (2 * a ^ 2) * (Real.exp (-2 * a) * (Real.cosh (κ * a) / Real.cosh a)) := by
    field_simp <;> ring
  rw [eqL]
  have hk : 0 ≤ ℓ * shortMargin ε a / (2 * a ^ 2) := by positivity
  have hq : ℓ / (2 * a ^ 2) ≤ 1 / (a * (1 - Real.exp (-(2 * a / ℓ)))) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have : ℓ * (1 - Real.exp (-(2 * a / ℓ))) ≤ 2 * a := by
      have h := mul_le_mul_of_nonneg_left (show 1 - Real.exp (-(2 * a / ℓ)) ≤ 2 * a / ℓ by linarith) hℓ.le
      rwa [mul_div_cancel₀ _ hℓ.ne'] at h
    nlinarith
  have he := Real.exp_pos (-η * a)
  have h4 : 0 ≤ 1 - 4 * ε := by linarith
  calc ℓ * shortMargin ε a / (2 * a ^ 2) * (Real.exp (-2 * a) * (Real.cosh (κ * a) / Real.cosh a))
      ≤ ℓ * shortMargin ε a / (2 * a ^ 2) * Real.exp (-η * a) := mul_le_mul_of_nonneg_left hEX hk
    _ = shortMargin ε a * (ℓ / (2 * a ^ 2)) * Real.exp (-η * a) := by ring
    _ ≤ (1 - 4 * ε) * (1 / (a * (1 - Real.exp (-(2 * a / ℓ))))) * Real.exp (-η * a) := by
        apply mul_le_mul_of_nonneg_right _ he.le
        exact mul_le_mul hm1 hq (by positivity) h4
    _ = (1 - 4 * ε) * (Real.exp (-η * a) / (a * (1 - Real.exp (-(2 * a / ℓ))))) := by ring

