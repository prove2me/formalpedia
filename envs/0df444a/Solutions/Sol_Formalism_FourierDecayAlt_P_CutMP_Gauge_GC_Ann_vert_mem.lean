-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.Ann.vert_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T07:16:28.884525+00:00
-- url     : https://prove2.me/submissions/94a84691-1bfd-4552-b643-93f5bafc109c

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BasePointMemHalfPlane
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ThetaAtBasePointZero
import Theorems.Thm_Formalism_FourierDecayAlt_P_CutMP_Gauge_GC_Ann_exp_base_point_eq

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
theorem _root_.solution (hTT : 0 ≤ TT) (θ : ℝ) : x0 TT + (θ : ℂ) * I ∈ Hh TT := by
  show TT < Complex.normSq (Complex.exp (x0 TT + (θ : ℂ) * I))
  rw [Complex.exp_add, exp_base_point_eq hTT, Complex.normSq_mul, Complex.normSq_ofReal,
    Complex.normSq_eq_norm_sq (Complex.exp _), Complex.norm_exp_ofReal_mul_I]
  nlinarith
end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.Ann
