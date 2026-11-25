-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.Ph.continuousOn_dZ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T07:16:25.380017+00:00
-- url     : https://prove2.me/submissions/606d6c23-3292-4026-8f49-3eb57de44628

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
theorem _root_.solution {TT : ℝ} {u : ℂ → ℂ} (hu : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) u (AnnT TT)) :
    ContinuousOn (NF.dZ u) (AnnT TT) := by
  have hf := hu.continuousOn_fderiv_of_isOpen (isOpen_annT TT) (by simp)
  have e : NF.dZ u = fun ζ => (1 / 2 : ℂ) * (fderiv ℝ u ζ 1 - Complex.I * fderiv ℝ u ζ Complex.I) := rfl
  rw [e]
  exact continuousOn_const.mul ((hf.clm_apply continuousOn_const).sub
    (continuousOn_const.mul (hf.clm_apply continuousOn_const)))
end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.Ph
