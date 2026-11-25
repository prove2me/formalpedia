-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.Ann.th_shift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T08:25:38.586397+00:00
-- url     : https://prove2.me/submissions/4baf01e7-c243-42f0-8569-17a5680f519f

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ImCircleIntegral
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ThShiftInt
import Theorems.Thm_Formalism_FourierDecayAlt_P_CutMP_Gauge_GC_Ann_Hh_add_one
import Theorems.Thm_Formalism_FourierDecayAlt_P_CutMP_Gauge_GC_Ann_base_point_mem_half_plane
import Theorems.Thm_Formalism_FourierDecayAlt_P_CutMP_Gauge_GC_Ann_bet_periodic
import Theorems.Thm_Formalism_FourierDecayAlt_P_CutMP_Gauge_GC_Ann_convex_Hh
import Theorems.Thm_Formalism_FourierDecayAlt_P_CutMP_Gauge_GC_Ann_hasFDerivAt_th
import Theorems.Thm_Formalism_FourierDecayAlt_P_CutMP_Gauge_GC_Ann_isOpen_Hh
import Theorems.Thm_Formalism_FourierDecayAlt_P_CutMP_Gauge_GC_Ann_th_top
import Theorems.Thm_Formalism_FourierDecayAlt_P_CutMP_Gauge_GC_Ann_theta_at_base_point_zero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Set Filter Topology Complex MeasureTheory intervalIntegral
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CutMP Formalism.FourierDecayAlt.P.CutMP.Gauge Formalism.FourierDecayAlt.P.CutMP.Gauge.GC Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.Ann
noncomputable section
variable {TT : ℝ} {α : ℂ → ℂ}
namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.Ann
theorem _root_.solution (hTT : 0 ≤ TT) (hα : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) α (An TT))
    (hcurv : ∀ ζ : ℂ, TT < Complex.normSq ζ → (wZb α ζ).re = 0) {w : ℂ} (hw : w ∈ Hh TT) :
    th TT α (w + 2 * Real.pi * I) = th TT α w + 2 * (circleIntegral α 0 (TT + 1)).im := by
  have hc : ∀ z ∈ Hh TT, HasFDerivAt (fun z => th TT α (z + 2 * Real.pi * I) - th TT α z)
      (0 : ℂ →L[ℝ] ℝ) z := by
    intro z hz
    have h1 : HasFDerivAt (fun z => th TT α (z + 2 * Real.pi * I)) (om α (z + 2 * Real.pi * I)) z := by
      have := (hasFDerivAt_th hTT hα hcurv (Hh_add_one hz)).comp z
        ((hasFDerivAt_id z).add_const (2 * Real.pi * I))
      exact this
    have h2 := hasFDerivAt_th hTT hα hcurv hz
    have hom : om α (z + 2 * Real.pi * I) = om α z := by
      have := bet_periodic α z 1
      simp only [Int.cast_one, one_mul] at this
      simp only [om, this]
    have := h1.sub h2
    rwa [hom, sub_self] at this
  have hconst := (convex_Hh TT).is_const_of_fderivWithin_eq_zero
    (fun z hz => (hc z hz).differentiableAt.differentiableWithinAt)
    (fun z hz => (hc z hz).hasFDerivWithinAt.fderivWithin ((isOpen_Hh TT).uniqueDiffWithinAt hz))
    (base_point_mem_half_plane hTT) hw
  rw [th_top hTT hα, theta_at_base_point_zero, sub_zero] at hconst
  linarith
end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.Ann
