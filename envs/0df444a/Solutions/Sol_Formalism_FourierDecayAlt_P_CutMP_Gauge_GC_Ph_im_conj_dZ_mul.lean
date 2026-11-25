-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.Ph.im_conj_dZ_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T07:09:08.317992+00:00
-- url     : https://prove2.me/submissions/4478dd3e-e5d2-467c-bb9d-23c8f1180290

import Definitions.Def_Formalism_HermitianCurvature_StatementNF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutGCoreGTCHolPh
import Theorems.Thm_Formalism_FourierDecayAlt_P_CutMP_Gauge_GC_Ph_re_conj_fderiv

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
    (star (u ζ) * NF.dZ u ζ * h).im = (star (u ζ) * fderiv ℝ u ζ h).im / 2 := by
  have hr1 := re_conj_fderiv hu h1 hζ 1
  have hrI := re_conj_fderiv hu h1 hζ Complex.I
  have hh : h = h.re • (1 : ℂ) + h.im • Complex.I := by
    apply Complex.ext <;> simp
  have hlin : fderiv ℝ u ζ h = h.re • fderiv ℝ u ζ 1 + h.im • fderiv ℝ u ζ Complex.I := by
    conv_lhs => rw [hh]
    rw [map_add, map_smul, map_smul]
  rw [hlin]
  simp only [NF.dZ]
  simp [Complex.mul_re, Complex.mul_im, Complex.star_def] at hr1 hrI ⊢
  linear_combination (h.im / 2) * hr1 - (h.re / 2) * hrI
end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.Ph
