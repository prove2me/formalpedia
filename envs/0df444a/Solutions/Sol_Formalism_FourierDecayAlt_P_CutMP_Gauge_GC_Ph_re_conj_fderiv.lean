-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.Ph.re_conj_fderiv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T06:58:51.548038+00:00
-- url     : https://prove2.me/submissions/602deb35-f67d-4c43-8cf6-63df122f0b86

import Definitions.Def_Formalism_HermitianCurvature_StatementNF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutGCoreGTCHolPh
import Theorems.Thm_Formalism_FourierDecayAlt_P_CutMP_Gauge_GC_Ph_isOpen_annT

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex MeasureTheory
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CutMP Formalism.FourierDecayAlt.P.CutMP.Gauge Formalism.FourierDecayAlt.P.CutMP.Gauge.GC Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.Ph
namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.Ph
theorem _root_.solution {TT : ℝ} {u : ℂ → ℂ} (hu : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) u (AnnT TT))
    (h1 : ∀ ζ ∈ AnnT TT, ‖u ζ‖ = 1) {ζ : ℂ} (hζ : ζ ∈ AnnT TT) (h : ℂ) :
    (star (u ζ) * fderiv ℝ u ζ h).re = 0 := by
  have hopen := isOpen_annT TT
  have hd : DifferentiableAt ℝ u ζ := (hu.differentiableOn (by simp)).differentiableAt (hopen.mem_nhds hζ)
  have hP := hd.hasFDerivAt.star.mul hd.hasFDerivAt
  have hconst : (fun w => star (u w) * u w) =ᶠ[nhds ζ] fun _ => (1 : ℂ) := by
    filter_upwards [hopen.mem_nhds hζ] with w hw
    have hn := h1 w hw
    rw [mul_comm]
    have e : u w * star (u w) = (Complex.normSq (u w) : ℂ) := Complex.mul_conj _
    rw [e, Complex.normSq_eq_norm_sq, hn]
    simp
  have hz := hP.fderiv.symm.trans (hconst.fderiv_eq.trans (hasFDerivAt_const (𝕜 := ℝ) (1 : ℂ) ζ).fderiv)
  have hv := congrArg (fun L => (L h).re) hz
  simp [Complex.mul_re, Complex.star_def] at hv
  simp [Complex.mul_re, Complex.star_def]
  linarith
end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.Ph
