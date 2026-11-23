-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.LEx2.L3
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:24:48.134009+00:00
-- url     : https://prove2.me/submissions/f3fbf891-fc22-447c-9343-d3f374554923

import Definitions.Def_Formalism_HermitianCurvature_StatementLE
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MeasIterDeriv
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ThetaLimit
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeightedL2BoundedMul
import Theorems.Thm_Formalism_FourierDecayAlt_P_LEx2_meas_ld
import Theorems.Thm_Formalism_FourierDecayAlt_P_LEx2_smoothLog_sc


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.LEx2
open Formalism.FourierDecayAlt.LE
open MeasureTheory Filter Topology Finset
open scoped ComplexConjugate
namespace Formalism.FourierDecayAlt.P.LEx2
theorem _root_.solution (hC : E.CauchyTheta) (hCT : CutTheta) (hTS : ThetaSmooth) (hTR : ThetaRange) (B : Base) (c : Cut)
    (σ ε : ℝ) (h4 : 4 ≤ σ) (hε : 0 < ε) (p : ℕ) (h : B.Ω → ℂ) (hm : AEStronglyMeasurable h B.μ) (b : B.Ω → ℝ)
    (hb : Integrable b B.μ) (hbd : ∀ ω, th ε σ (B.G ω) * ‖h ω‖ ≤ b ω) :
    (∀ ε₂ : ℝ, 0 < ε₂ → Integrable (fun ω => (ld p (fun y => c.sc ε₂ 1 y * th ε σ y) (B.G ω) : ℂ) * h ω) B.μ) ∧
    Tendsto (fun ε₂ : ℝ => ∫ ω, (ld p (fun y => c.sc ε₂ 1 y * th ε σ y) (B.G ω) : ℂ) * h ω ∂B.μ) (𝓝[>] 0)
      (𝓝 (∫ ω, (ld p (th ε σ) (B.G ω) : ℂ) * h ω ∂B.μ)) := by
  obtain ⟨C, hCb⟩ := hCT hC c σ ε h4 hε p
  have hsm : ∀ ε₂ : ℝ, SmoothLog (fun y => c.sc ε₂ 1 y * th ε σ y) := fun ε₂ =>
    ContDiff.mul (smoothLog_sc c ε₂ 1) (hTS ε σ hε)
  have hmeas : ∀ ε₂ : ℝ, AEStronglyMeasurable
      (fun ω => (ld p (fun y => c.sc ε₂ 1 y * th ε σ y) (B.G ω) : ℂ) * h ω) B.μ := fun ε₂ =>
    ((Complex.measurable_ofReal.comp ((meas_ld p _ (hsm ε₂)).comp B.G_meas)).aestronglyMeasurable.mul hm)
  have hbound : ∀ ε₂ : ℝ, 0 < ε₂ → ∀ ω,
      ‖(ld p (fun y => c.sc ε₂ 1 y * th ε σ y) (B.G ω) : ℂ) * h ω‖ ≤ |C| * b ω := by
    intro ε₂ h2 ω
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have a := (hCb ε₂ (B.G ω) h2 (B.G_pos ω)).1
    have t0 := (hTR ε σ (B.G ω) hε (by linarith) (B.G_pos ω)).1.le
    calc _ ≤ (C * th ε σ (B.G ω)) * ‖h ω‖ := mul_le_mul_of_nonneg_right a (norm_nonneg _)
      _ = C * (th ε σ (B.G ω) * ‖h ω‖) := by ring
      _ ≤ |C| * (th ε σ (B.G ω) * ‖h ω‖) :=
          mul_le_mul_of_nonneg_right (le_abs_self C) (mul_nonneg t0 (norm_nonneg _))
      _ ≤ |C| * b ω := mul_le_mul_of_nonneg_left (hbd ω) (abs_nonneg _)
  refine ⟨fun ε₂ h2 => Integrable.mono' (hb.const_mul |C|) (hmeas ε₂) (Eventually.of_forall (hbound ε₂ h2)), ?_⟩
  refine tendsto_integral_filter_of_dominated_convergence (fun ω => |C| * b ω) (Eventually.of_forall hmeas) ?_
    (hb.const_mul _) ?_
  · filter_upwards [self_mem_nhdsWithin] with ε₂ h2
    exact Eventually.of_forall (hbound ε₂ h2)
  · refine Eventually.of_forall fun ω => ?_
    apply tendsto_const_nhds.congr'
    have e1 : ∀ᶠ ε₂ : ℝ in 𝓝[>] 0, ε₂ < B.G ω :=
      (eventually_lt_nhds (B.G_pos ω)).filter_mono nhdsWithin_le_nhds
    filter_upwards [self_mem_nhdsWithin, e1] with ε₂ h2 h3
    rw [(hCb ε₂ (B.G ω) h2 (B.G_pos ω)).2 h3]
end Formalism.FourierDecayAlt.P.LEx2
