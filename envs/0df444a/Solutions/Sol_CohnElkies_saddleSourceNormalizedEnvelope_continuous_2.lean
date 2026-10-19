-- Prove2me | solution 2 for CohnElkies.saddleSourceNormalizedEnvelope_continuous
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:12:56.850607+00:00
-- url     : https://prove2.me/submissions/c15a659c-66dd-4484-b976-cec05bf0e655

import Mathlib
import Definitions.Def_SpherePacking
set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter Set MeasureTheory
open scoped Topology


theorem solution
    {ε ℓ u : ℝ}
    (hε : 0 < ε) (hℓ : 0 < ℓ) (hu : -1 < u)
    (horder : shortCutoff ε ≤ shortEndpoint ε) :
    Continuous (saddleSourceNormalizedEnvelope ε ℓ u) := by
  have hphase := (mellinShellPhase_differentiable hε horder).continuous
  have hc : Continuous (saddleSourceMellinContour ℓ u) := by
    unfold saddleSourceMellinContour; fun_prop
  have hG : Continuous (fun T : ℝ => Complex.Gamma (saddleSourceMellinContour ℓ u T / 2)) := by
    rw [continuous_iff_continuousAt]
    intro T
    refine ContinuousAt.comp (g := Complex.Gamma) ?_ (hc.div_const 2).continuousAt
    apply (Complex.differentiableAt_Gamma _ _).continuousAt
    intro m h
    have h2 := congrArg Complex.re h
    unfold saddleSourceMellinContour at h2
    simp at h2
    have h3 : 0 < ℓ * (1 + u) := mul_pos hℓ (by linarith)
    have h4 : (0:ℝ) ≤ m := m.cast_nonneg
    nlinarith
  unfold saddleSourceNormalizedEnvelope
  apply Continuous.div_const
  unfold saddleMellinEnvelope
  exact ((Continuous.cexp (((continuous_const.sub hc).mul continuous_const).div_const _)).mul hG).mul
    (Continuous.cexp (continuous_const.mul
      (hphase.comp ((continuous_const.mul (hc.sub continuous_const)).div_const _))))

