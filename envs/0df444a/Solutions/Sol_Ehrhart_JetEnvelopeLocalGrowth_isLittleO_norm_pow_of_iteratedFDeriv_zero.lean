-- Prove2me | solution 1 for Ehrhart.JetEnvelopeLocalGrowth.isLittleO_norm_pow_of_iteratedFDeriv_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:14.10863+00:00
-- url     : https://prove2.me/submissions/5ccb699c-79ce-4068-b405-70e1fb5ff211

import Mathlib
import Definitions.Def_EhrhartVolumeInequality

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.JetEnvelopeLocalGrowth
open Set Filter MeasureTheory Module Metric Asymptotics
open ActualJetUpperEnvelope JetEnvelopeSlopeConvergence JetEnvelopeRightDerivative
open scoped BigOperators Topology ENNReal InnerProductSpace
universe u v
namespace Ehrhart.JetEnvelopeLocalGrowth
theorem _root_.solution
    {E : Type u} {F : Type (max u v)}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    (f : E → F) (hf : ContDiff ℂ ⊤ f)
    (p : E) (j : ℕ)
    (hzero : ∀ i : ℕ, i ≤ j → iteratedFDeriv ℂ i f p = 0) :
    (fun z : E => f z - f p) =o[𝓝 p]
      (fun z : E => ‖z - p‖ ^ j) := by
  induction j generalizing F f with
  | zero =>
      have hc : ContinuousAt f p := hf.continuous.continuousAt
      simpa [Asymptotics.isLittleO_one_iff] using
        hc.tendsto.sub_const (f p)
  | succ j ih =>
      have hdf : ContDiff ℂ ⊤ (fderiv ℂ f) :=
        hf.fderiv_right (by simp)
      have hdzero :
          ∀ i : ℕ, i ≤ j →
            iteratedFDeriv ℂ i (fderiv ℂ f) p = 0 := by
        intro i hi
        apply norm_eq_zero.mp
        rw [norm_iteratedFDeriv_fderiv,
          hzero (i + 1) (by omega), norm_zero]
      have hdp : fderiv ℂ f p = 0 := by
        have h := hdzero 0 (Nat.zero_le j)
        apply norm_eq_zero.mp
        have hn := congrArg norm h
        simpa [norm_iteratedFDeriv_zero] using hn
      have hsmall :
          (fderiv ℂ f) =o[𝓝 p]
            (fun z : E => ‖z - p‖ ^ j) := by
        simpa [hdp] using ih (fderiv ℂ f) hdf hdzero
      have hmean := (convex_univ : Convex ℝ (Set.univ : Set E))
        |>.isLittleO_pow_succ (Set.mem_univ p)
          (fun z _ =>
            (hf.differentiable (by simp)).differentiableAt.hasFDerivAt
              |>.hasFDerivWithinAt)
          (by simpa using hsmall)
      simpa using hmean
end Ehrhart.JetEnvelopeLocalGrowth
