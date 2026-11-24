-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.PrimesInProgressions.Dens.EtaPartialSums.G_differentiableOn
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:39:48.678808+00:00
-- url     : https://prove2.me/submissions/c11f46bb-bda9-4545-9536-111bc569baeb

import Definitions.Def_Formalism_LFunctionBounds_LFunctionBoundsProofs_LFunctionEqGOfOneLt
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTDensLsA
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_Dens_EtaPartialSums_dterm_zero
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_Dens_EtaPartialSums_norm_dterm_le
import Theorems.Thm_Formalism_FX_LFunctionPartialSum_dterm_zero
import Theorems.Thm_Formalism_FX_LFunctionPartialSum_norm_dterm_le


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Filter Topology
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.PrimesInProgressions Formalism.HermitianLattices.Ext.PrimesInProgressions.Dens Formalism.HermitianLattices.Ext.PrimesInProgressions.Dens.EtaPartialSums
open Formalism.FX.LFunctionPartialSum
variable (f : ℕ → ℂ)
namespace Formalism.HermitianLattices.Ext.PrimesInProgressions.Dens.EtaPartialSums
theorem _root_.solution {B : ℝ} (hB : ∀ M, ‖Ap f M‖ ≤ B) :
    DifferentiableOn ℂ (G f) {s : ℂ | 0 < s.re} := by
  have hB0 : 0 ≤ B := le_trans (norm_nonneg _) (hB 0)
  intro s0 hs0
  have hσ : 0 < s0.re := hs0
  have hU : IsOpen ({w : ℂ | s0.re / 2 < w.re} ∩ Metric.ball s0 1) :=
    (isOpen_lt continuous_const Complex.continuous_re).inter Metric.isOpen_ball
  have hmem : s0 ∈ ({w : ℂ | s0.re / 2 < w.re} ∩ Metric.ball s0 1) :=
    ⟨show s0.re / 2 < s0.re by linarith, Metric.mem_ball_self one_pos⟩
  have hD : DifferentiableOn ℂ (fun w => ∑' n, dterm f w n)
      ({w : ℂ | s0.re / 2 < w.re} ∩ Metric.ball s0 1) := by
    refine Complex.differentiableOn_tsum_of_summable_norm (F := fun n w => dterm f w n)
      (u := fun n : ℕ => B * ((‖s0‖ + 1) * (n : ℝ) ^ (-(s0.re / 2) - 1))) ?_ ?_ hU ?_
    · exact ((Real.summable_nat_rpow.2 (by linarith)).mul_left _).mul_left _
    · intro n w hw
      have h1 : s0.re / 2 < w.re := hw.1
      have hw0 : -w ≠ 0 := by
        intro h
        rw [neg_eq_zero] at h
        rw [h, Complex.zero_re] at h1
        linarith
      refine DifferentiableAt.differentiableWithinAt ?_
      show DifferentiableAt ℂ (fun w => Ap f n * ((n : ℂ) ^ (-w) - ((n : ℂ) + 1) ^ (-w))) w
      have hneg : DifferentiableAt ℂ (fun w : ℂ => -w) w := differentiableAt_id.neg
      have ha : DifferentiableAt ℂ (fun w : ℂ => (n : ℂ) ^ (-w)) w := hneg.const_cpow (Or.inr hw0)
      have hb : DifferentiableAt ℂ (fun w : ℂ => ((n : ℂ) + 1) ^ (-w)) w :=
        hneg.const_cpow (Or.inr hw0)
      exact (ha.sub hb).const_mul (Ap f n)
    · intro n w hw
      have h1 : s0.re / 2 < w.re := hw.1
      have h2 : dist w s0 < 1 := hw.2
      have hwre : 0 < w.re := by linarith
      show ‖dterm f w n‖ ≤ B * ((‖s0‖ + 1) * (n : ℝ) ^ (-(s0.re / 2) - 1))
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · rw [dterm_zero, norm_zero]
        exact mul_nonneg hB0 (mul_nonneg (by positivity) (Real.rpow_nonneg (Nat.cast_nonneg _) _))
      · refine le_trans (norm_dterm_le f hB hwre n) (mul_le_mul_of_nonneg_left ?_ hB0)
        have h3 : ‖w - s0‖ < 1 := by rwa [dist_eq_norm] at h2
        have h4 := norm_sub_norm_le w s0
        have hw1 : ‖w‖ ≤ ‖s0‖ + 1 := by linarith
        have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
        have hpow : (n : ℝ) ^ (-w.re - 1) ≤ (n : ℝ) ^ (-(s0.re / 2) - 1) :=
          Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)
        exact mul_le_mul hw1 hpow (Real.rpow_nonneg (Nat.cast_nonneg _) _) (by positivity)
  exact (hD.differentiableAt (hU.mem_nhds hmem)).differentiableWithinAt
end Formalism.HermitianLattices.Ext.PrimesInProgressions.Dens.EtaPartialSums
