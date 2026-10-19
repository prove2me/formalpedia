-- Prove2me | solution 1 for CohnElkies.exists_stripPoissonKernel_uniform_abs_moment
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:32.753002+00:00
-- url     : https://prove2.me/submissions/7804e583-e79e-4f72-aac0-09db6001bf64

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_stripBottomMass_lt_one
import Theorems.Thm_CohnElkies_stripPoissonKernel_pos
import Theorems.Thm_CohnElkies_stripPoissonKernel_integrable
import Theorems.Thm_CohnElkies_integral_stripPoissonKernel
import Theorems.Thm_CohnElkies_stripPoissonKernel_le_center_of_lower_of_abs_ge
import Theorems.Thm_CohnElkies_stripPoissonKernel_le_exponentialMajorant_of_nonneg
import Theorems.Thm_CohnElkies_harmonic_stripPoissonExponentialMajorant_abs_integrable
import Theorems.Thm_CohnElkies_harmonic_stripPoissonKernel_zero_abs_integrable
import Theorems.Thm_CohnElkies_harmonic_stripPoissonKernel_abs_integrable

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Asymptotics Bornology Complex Filter Function MeasureTheory Metric Set
open scoped Filter FourierTransform Real SchwartzMap Topology
namespace CohnElkies
theorem _root_.solution :
    ∃ M : ℝ, 0 ≤ M ∧
      ∀ σ : ℝ, -1 < σ → σ < 1 →
        (∫ T : ℝ,
          stripPoissonKernel σ T * |T|) ≤ M := by
  let C : ℝ :=
    1 / (1 - (Real.cosh (Real.pi / 2))⁻¹)
  let J : ℝ :=
    ∫ T : ℝ, stripPoissonKernel 0 T * |T|
  let E : ℝ :=
    ∫ T : ℝ,
      stripPoissonExponentialMajorant T * |T|
  let M : ℝ := 1 + C * J + E
  have harg : Real.pi / 2 ≠ 0 :=
    (half_pos Real.pi_pos).ne'
  have hcosh : 1 < Real.cosh (Real.pi / 2) :=
    Real.one_lt_cosh.mpr harg
  have hC : 0 < C := by
    try dsimp [C]
    have hpositive := Real.cosh_pos (Real.pi / 2)
    have hinv := (inv_lt_one₀ hpositive).mpr hcosh
    exact one_div_pos.mpr (by linarith)
  have hJ : 0 ≤ J := by
    try dsimp [J]
    apply integral_nonneg
    intro T
    exact mul_nonneg
      (stripPoissonKernel_pos
        (by norm_num : (-1 : ℝ) < 0)
        (by norm_num : (0 : ℝ) < 1) T).le
      (abs_nonneg T)
  have hE : 0 ≤ E := by
    try dsimp [E]
    apply integral_nonneg
    intro T
    unfold stripPoissonExponentialMajorant
    positivity
  have hM : 0 ≤ M := by
    try dsimp [M]
    positivity
  refine ⟨M, hM, ?_⟩
  intro σ hbelow habove
  have hmoment :=
    harmonic_stripPoissonKernel_abs_integrable
      hbelow habove
  by_cases hσ : σ ≤ 0
  · let S : Set ℝ := {T : ℝ | 1 ≤ |T|}
    have hS : MeasurableSet S :=
      (isClosed_le continuous_const
        continuous_abs).measurableSet
    have hk := stripPoissonKernel_integrable
      hbelow habove
    have hcenter :=
      harmonic_stripPoissonKernel_zero_abs_integrable
    have hscaled : Integrable
        (fun T : ℝ =>
          C * (stripPoissonKernel 0 T * |T|)) :=
      hcenter.const_mul C
    have hfar :
        (∫ T in S,
          stripPoissonKernel σ T * |T|) ≤
          C * J := by
      calc
        (∫ T in S,
            stripPoissonKernel σ T * |T|) ≤
          ∫ T in S,
            C * (stripPoissonKernel 0 T * |T|) := by
          apply setIntegral_mono_on
            hmoment.integrableOn
            hscaled.integrableOn hS
          intro T hT
          have hcompare :=
            stripPoissonKernel_le_center_of_lower_of_abs_ge
              hbelow hσ
              (by norm_num : (0 : ℝ) < 1)
              (show (1 : ℝ) ≤ |T| from hT)
          have hCeq :
              1 / (1 -
                (Real.cosh (Real.pi * (1 : ℝ) / 2))⁻¹) =
                C := by
            try dsimp [C]
            congr 2
            ring_nf
          rw [hCeq] at hcompare
          nlinarith [mul_nonneg
            (sub_nonneg.mpr hcompare)
            (abs_nonneg T)]
        _ ≤ ∫ T : ℝ,
            C * (stripPoissonKernel 0 T * |T|) := by
          apply setIntegral_le_integral hscaled
          filter_upwards [] with T
          exact mul_nonneg hC.le
            (mul_nonneg
              (stripPoissonKernel_pos
                (by norm_num : (-1 : ℝ) < 0)
                (by norm_num : (0 : ℝ) < 1) T).le
              (abs_nonneg T))
        _ = C * J := by
          rw [integral_const_mul]
    have hnear :
        (∫ T in Sᶜ,
          stripPoissonKernel σ T * |T|) ≤ 1 := by
      calc
        (∫ T in Sᶜ,
            stripPoissonKernel σ T * |T|) ≤
          ∫ T in Sᶜ,
            stripPoissonKernel σ T := by
          apply setIntegral_mono_on
            hmoment.integrableOn
            hk.integrableOn hS.compl
          intro T hT
          have hTabs : |T| ≤ 1 := by
            have hnot : ¬ (1 : ℝ) ≤ |T| := by
              intro hge
              exact hT (show T ∈ S from hge)
            exact (lt_of_not_ge hnot).le
          have hkpos :=
            stripPoissonKernel_pos
              hbelow habove T
          nlinarith [mul_nonneg hkpos.le
            (sub_nonneg.mpr hTabs)]
        _ ≤ ∫ T : ℝ,
            stripPoissonKernel σ T := by
          apply setIntegral_le_integral hk
          filter_upwards [] with T
          exact (stripPoissonKernel_pos
            hbelow habove T).le
        _ = stripBottomMass σ :=
          integral_stripPoissonKernel hbelow habove
        _ ≤ 1 := (stripBottomMass_lt_one hbelow).le
    have hsplit := integral_add_compl hS hmoment
    try dsimp [M]
    nlinarith
  · have hσnonneg : 0 ≤ σ := le_of_not_ge hσ
    have hmajor :=
      harmonic_stripPoissonExponentialMajorant_abs_integrable
    have hineq :
        (∫ T : ℝ,
          stripPoissonKernel σ T * |T|) ≤ E := by
      try dsimp [E]
      apply integral_mono hmoment hmajor
      intro T
      apply mul_le_mul_of_nonneg_right
        (stripPoissonKernel_le_exponentialMajorant_of_nonneg
          hσnonneg habove T)
        (abs_nonneg T)
    try dsimp [M]
    nlinarith [mul_nonneg hC.le hJ]
end CohnElkies
