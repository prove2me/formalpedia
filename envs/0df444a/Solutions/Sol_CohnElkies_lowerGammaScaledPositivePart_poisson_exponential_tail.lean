-- Prove2me | solution 1 for CohnElkies.lowerGammaScaledPositivePart_poisson_exponential_tail
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:34.337066+00:00
-- url     : https://prove2.me/submissions/2a4da786-4566-4073-8cb1-c144d088b701

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_stripBottomMass_pos
import Theorems.Thm_CohnElkies_lowerGammaScaledPositivePart_integrable
import Theorems.Thm_CohnElkies_stripPoissonKernel_weighted_product_integrable
import Theorems.Thm_CohnElkies_stripPoissonKernel_le_mass_mul_exponential

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Metric Set
open scoped ENNReal Interval Topology
namespace CohnElkies
theorem _root_.solution
    {d : ℕ} (hd : 2 ≤ d) {c σ C S : ℝ}
    (hc : 0 < c) (hσ : 0 ≤ σ) (hσone : σ < 1)
    (hC : 0 < C)
    (hsupport :
      Function.support (lowerGammaScaledPositivePart d c) ⊆
        Icc (-C) C)
    (hmass :
      (∫ Y : ℝ, lowerGammaScaledPositivePart d c Y) ≤
        C * ((d : ℝ) / 2))
    (hS : C ≤ S) :
    (∫ Y : ℝ,
      stripPoissonKernel σ (S - Y) *
        lowerGammaScaledPositivePart d c Y) ≤
      (stripBottomMass σ * (Real.pi / 2) *
        Real.exp (-(Real.pi / 2) * (S - C))) *
          (C * ((d : ℝ) / 2)) := by
  have hbelow : -1 < σ := by linarith
  let E : ℝ :=
    stripBottomMass σ * (Real.pi / 2) *
      Real.exp (-(Real.pi / 2) * (S - C))
  have hE : 0 ≤ E := by
    apply (mul_nonneg_iff_of_pos_right hC).mp
    try dsimp [E]
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg (stripBottomMass_pos hσone).le
          (by positivity))
        (Real.exp_pos _).le)
      hC.le
  have hp := lowerGammaScaledPositivePart_integrable hd hc
  have hweighted := stripPoissonKernel_weighted_product_integrable
    hbelow hσone hp S
  have hmajor : Integrable
      (fun Y : ℝ => E * lowerGammaScaledPositivePart d c Y) :=
    hp.const_mul E
  calc
    (∫ Y : ℝ,
      stripPoissonKernel σ (S - Y) *
        lowerGammaScaledPositivePart d c Y) ≤
      ∫ Y : ℝ,
        E * lowerGammaScaledPositivePart d c Y := by
      apply integral_mono_ae hweighted hmajor
      filter_upwards [] with Y
      by_cases hzero : lowerGammaScaledPositivePart d c Y = 0
      · simp [hzero]
      · have hY := hsupport hzero
        have hdist : S - C ≤ |S - Y| := by
          rw [abs_of_nonneg (by linarith [hY.2] : 0 ≤ S - Y)]
          linarith [hY.2]
        have hexp :
            Real.exp (-(Real.pi / 2) * |S - Y|) ≤
              Real.exp (-(Real.pi / 2) * (S - C)) := by
          apply Real.exp_le_exp.mpr
          nlinarith [Real.pi_pos]
        have hkernel : stripPoissonKernel σ (S - Y) ≤ E := by
          calc
            stripPoissonKernel σ (S - Y) ≤
              stripBottomMass σ *
                stripPoissonExponentialMajorant (S - Y) :=
                stripPoissonKernel_le_mass_mul_exponential
                  hσ hσone (S - Y)
            _ = stripBottomMass σ *
                ((Real.pi / 2) *
                  Real.exp (-(Real.pi / 2) * |S - Y|)) := by
                rfl
            _ ≤ stripBottomMass σ *
                ((Real.pi / 2) *
                  Real.exp (-(Real.pi / 2) * (S - C))) := by
                apply mul_le_mul_of_nonneg_left
                · exact mul_le_mul_of_nonneg_left hexp
                    (by positivity)
                · exact (stripBottomMass_pos hσone).le
            _ = E := by
              try dsimp [E]
              ring
        exact mul_le_mul_of_nonneg_right hkernel
          (le_max_right _ _)
    _ = E *
      (∫ Y : ℝ, lowerGammaScaledPositivePart d c Y) := by
      rw [integral_const_mul]
    _ ≤ E * (C * ((d : ℝ) / 2)) :=
      mul_le_mul_of_nonneg_left hmass hE
    _ = (stripBottomMass σ * (Real.pi / 2) *
        Real.exp (-(Real.pi / 2) * (S - C))) *
          (C * ((d : ℝ) / 2)) := by
      rfl
end CohnElkies
