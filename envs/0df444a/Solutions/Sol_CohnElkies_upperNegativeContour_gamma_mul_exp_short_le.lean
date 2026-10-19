-- Prove2me | solution 1 for CohnElkies.upperNegativeContour_gamma_mul_exp_short_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:28.839589+00:00
-- url     : https://prove2.me/submissions/dffed0c3-056c-44f9-b086-59dd408060a8

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_upperGammaDamping_nonneg
import Theorems.Thm_CohnElkies_upperNegativeContour_shortDamping_le_gamma
import Theorems.Thm_CohnElkies_saddleNegativeGammaRate_pos
import Theorems.Thm_CohnElkies_one_le_saddleNegativeContourOrdinate
import Theorems.Thm_CohnElkies_saddleNegativeContourOrdinate_add_rate_le_three
import Theorems.Thm_CohnElkies_upperNegativeContour_reflectedGamma_damping_exp_le_cosh
import Theorems.Thm_CohnElkies_upperNegativeHalfGamma_norm_eq_reflected_damping
import Theorems.Thm_CohnElkies_upper_log_cosh_ge_abs_sub_log_two

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped Topology BigOperators
namespace CohnElkies
theorem _root_.solution
    {ε ℓ : ℝ}
    (hε : 0 < ε) (hεsmall : ε ≤ 1 / 4)
    (hℓ : 0 < ℓ) (N : ℕ)
    (hN : 2 * (((N + 1 : ℕ) : ℝ)) ≤ ℓ)
    (horder : shortCutoff ε ≤ shortEndpoint ε)
    (hmargin : ∀ a ∈ Icc (shortCutoff ε) (shortEndpoint ε),
      0 ≤ shortMargin ε a)
    (s : ℝ) :
    ‖Complex.Gamma (upperNegativeHalfGammaArgument N s)‖ *
      Real.exp
        (upperShortShellDamping ε ℓ
          (-saddleNegativeContourOrdinate ℓ N - 1)
          (-s / ℓ)) ≤
      (Real.pi / Real.Gamma ((N : ℝ) + 3 / 2)) *
        Real.exp (2 * ε * Real.log 2) *
          Real.exp (-ε * Real.pi * |s|) := by
  let κ : ℝ := saddleNegativeContourOrdinate ℓ N
  let η : ℝ := saddleNegativeGammaRate ℓ N
  let T : ℝ := -s / ℓ
  let D : ℝ := upperGammaDamping ℓ η T
  let C : ℝ := Real.cosh (Real.pi * (s / 2))
  have hκ : 1 ≤ κ := one_le_saddleNegativeContourOrdinate hℓ N
  have hη : 0 < η := saddleNegativeGammaRate_pos hℓ N
  have hκη : κ + η ≤ 3 :=
    saddleNegativeContourOrdinate_add_rate_le_three hℓ N hN
  have hshort := upperNegativeContour_shortDamping_le_gamma
    hε hεsmall hℓ hκ hη hκη horder hmargin T
  have hD : 0 ≤ D := upperGammaDamping_nonneg hℓ T
  have hC : 0 < C := Real.cosh_pos _
  have hreflect :=
    upperNegativeContour_reflectedGamma_damping_exp_le_cosh
      hℓ N s
  have hDlog : 2 * D ≤ Real.log C := by
    apply Real.exp_le_exp.mp
    rw [Real.exp_log hC]
    exact hreflect
  have hlog := upper_log_cosh_ge_abs_sub_log_two
    (Real.pi * (s / 2))
  have hfactor : 0 ≤ 2 - 4 * ε := by linarith
  have hphase :
      (2 - 4 * ε) * D - Real.log C ≤
        -(2 * ε) * Real.log C := by
    nlinarith [mul_nonneg hfactor
      (show 0 ≤ Real.log C - 2 * D by linarith)]
  have hlogphase :
      -(2 * ε) * Real.log C ≤
        2 * ε * Real.log 2 - ε * Real.pi * |s| := by
    have habs : |Real.pi * (s / 2)| =
        Real.pi * |s| / 2 := by
      rw [abs_mul, abs_of_pos Real.pi_pos, abs_div,
        abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      ring
    rw [habs] at hlog
    nlinarith [mul_nonneg (show 0 ≤ 2 * ε by positivity)
      (show 0 ≤ Real.log C -
        (Real.pi * |s| / 2 - Real.log 2) by
        try dsimp [C]
        linarith)]
  have hΓ : 0 < Real.Gamma ((N : ℝ) + 3 / 2) := by
    apply Real.Gamma_pos_of_pos
    positivity
  have hpref : 0 ≤ Real.pi /
      Real.Gamma ((N : ℝ) + 3 / 2) := by positivity
  rw [upperNegativeHalfGamma_norm_eq_reflected_damping
    hℓ N s]
  change
    ((Real.pi / Real.Gamma ((N : ℝ) + 3 / 2)) *
      Real.exp D / C) *
        Real.exp (upperShortShellDamping ε ℓ (-κ - 1) T) ≤
      (Real.pi / Real.Gamma ((N : ℝ) + 3 / 2)) *
        Real.exp (2 * ε * Real.log 2) *
          Real.exp (-ε * Real.pi * |s|)
  have hshortexp :
      Real.exp (upperShortShellDamping ε ℓ (-κ - 1) T) ≤
        Real.exp ((1 - 4 * ε) * D) :=
    Real.exp_le_exp.mpr hshort
  calc
    ((Real.pi / Real.Gamma ((N : ℝ) + 3 / 2)) *
      Real.exp D / C) *
        Real.exp (upperShortShellDamping ε ℓ (-κ - 1) T) ≤
      ((Real.pi / Real.Gamma ((N : ℝ) + 3 / 2)) *
        Real.exp D / C) *
          Real.exp ((1 - 4 * ε) * D) := by
            gcongr
    _ = (Real.pi / Real.Gamma ((N : ℝ) + 3 / 2)) *
        Real.exp ((2 - 4 * ε) * D - Real.log C) := by
      have he :
          Real.exp D * Real.exp ((1 - 4 * ε) * D) =
            Real.exp ((2 - 4 * ε) * D) := by
        rw [← Real.exp_add]
        congr 1
        ring
      rw [Real.exp_sub, Real.exp_log hC]
      calc
        ((Real.pi / Real.Gamma ((N : ℝ) + 3 / 2)) *
          Real.exp D / C) *
            Real.exp ((1 - 4 * ε) * D) =
          (Real.pi / Real.Gamma ((N : ℝ) + 3 / 2)) *
            (Real.exp D *
              Real.exp ((1 - 4 * ε) * D)) / C := by ring
        _ = (Real.pi / Real.Gamma ((N : ℝ) + 3 / 2)) *
            Real.exp ((2 - 4 * ε) * D) / C := by rw [he]
        _ = (Real.pi / Real.Gamma ((N : ℝ) + 3 / 2)) *
            (Real.exp ((2 - 4 * ε) * D) / C) := by ring
    _ ≤ (Real.pi / Real.Gamma ((N : ℝ) + 3 / 2)) *
        Real.exp (-(2 * ε) * Real.log C) := by
      gcongr
    _ ≤ (Real.pi / Real.Gamma ((N : ℝ) + 3 / 2)) *
        Real.exp
          (2 * ε * Real.log 2 - ε * Real.pi * |s|) := by
      gcongr
    _ = (Real.pi / Real.Gamma ((N : ℝ) + 3 / 2)) *
        Real.exp (2 * ε * Real.log 2) *
          Real.exp (-ε * Real.pi * |s|) := by
      rw [show 2 * ε * Real.log 2 - ε * Real.pi * |s| =
        (2 * ε * Real.log 2) + (-ε * Real.pi * |s|) by ring,
        Real.exp_add]
      ring
end CohnElkies
