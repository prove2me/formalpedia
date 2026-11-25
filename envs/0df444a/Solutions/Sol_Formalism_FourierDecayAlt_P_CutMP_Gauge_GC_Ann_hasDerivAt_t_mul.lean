-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.Ann.hasDerivAt_t_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:32:08.93189+00:00
-- url     : https://prove2.me/submissions/7a33b96b-77a2-43a8-a43c-0038d1361f2d

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HasDerivAtTMul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Set Filter Topology MeasureTheory intervalIntegral
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CutMP Formalism.FourierDecayAlt.P.CutMP.Gauge Formalism.FourierDecayAlt.P.CutMP.Gauge.GC Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.Ann
noncomputable section
variable {ω : ℂ → ℂ →L[ℝ] ℝ} {S : Set ℂ} {w₀ : ℂ}
namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.Ann
theorem _root_.solution (hω : ∀ p ∈ S, HasFDerivAt ω (fderiv ℝ ω p) p)
    (hsym : ∀ p ∈ S, ∀ h k : ℂ, fderiv ℝ ω p h k = fderiv ℝ ω p k h) {w : ℂ} {t : ℝ}
    (hγ : w₀ + (t : ℂ) * (w - w₀) ∈ S) (h : ℂ) :
    HasDerivAt (fun s : ℝ => s * ω (w₀ + (s : ℂ) * (w - w₀)) h)
      (ω (w₀ + (t : ℂ) * (w - w₀)) h + t * fderiv ℝ ω (w₀ + (t : ℂ) * (w - w₀)) h (w - w₀)) t := by
  have hγd : HasDerivAt (fun s : ℝ => w₀ + (s : ℂ) * (w - w₀)) (w - w₀) t := by
    have := ((Complex.ofRealCLM.hasDerivAt (x := t)).mul_const (w - w₀)).const_add w₀
    simpa using this
  have h1 : HasDerivAt (fun s : ℝ => ω (w₀ + (s : ℂ) * (w - w₀))) (fderiv ℝ ω (w₀ + (t : ℂ) * (w - w₀)) (w - w₀)) t :=
    (hω _ hγ).comp_hasDerivAt t hγd
  have h2 : HasDerivAt (fun s : ℝ => ω (w₀ + (s : ℂ) * (w - w₀)) h)
      (fderiv ℝ ω (w₀ + (t : ℂ) * (w - w₀)) (w - w₀) h) t := by
    exact (ContinuousLinearMap.apply ℝ ℝ h).hasFDerivAt.comp_hasDerivAt t h1
  have h3 := (hasDerivAt_id t).mul h2
  refine h3.congr_deriv ?_
  rw [hsym _ hγ h (w - w₀)]
  simp
end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.Ann
