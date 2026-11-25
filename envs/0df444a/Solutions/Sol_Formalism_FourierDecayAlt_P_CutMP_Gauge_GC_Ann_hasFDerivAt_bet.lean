-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.Ann.hasFDerivAt_bet
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T07:26:17.310191+00:00
-- url     : https://prove2.me/submissions/cad57bed-53a0-4c9a-899f-83739d9779e1

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FderivDecomp
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BasePointMemHalfPlane
import Theorems.Thm_Formalism_FourierDecayAlt_P_CutMP_Gauge_GC_Ann_isOpen_An
import Theorems.Thm_Formalism_FourierDecayAlt_P_CutMP_Gauge_GC_Ann_exp_mem_An
import Theorems.Thm_Formalism_FourierDecayAlt_P_CutMP_Gauge_GC_Ann_hasFDerivAt_exp_real

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Set Filter Topology Complex
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CutMP Formalism.FourierDecayAlt.P.CutMP.Gauge Formalism.FourierDecayAlt.P.CutMP.Gauge.GC Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.Ann
noncomputable section
variable {TT : ℝ} {α : ℂ → ℂ}
namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.Ann
theorem _root_.solution (hα : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) α (An TT)) {w : ℂ} (hw : w ∈ Hh TT) :
    HasFDerivAt (bet α)
      (α (Complex.exp w) • (ContinuousLinearMap.mul ℝ ℂ) (Complex.exp w) +
        Complex.exp w • (fderiv ℝ α (Complex.exp w)).comp ((ContinuousLinearMap.mul ℝ ℂ) (Complex.exp w))) w := by
  have he := hasFDerivAt_exp_real w
  have hmem : Complex.exp w ∈ An TT := exp_mem_An hw
  have hdα : DifferentiableAt ℝ α (Complex.exp w) :=
    (hα.contDiffAt ((isOpen_An TT).mem_nhds hmem)).differentiableAt
      (by first | simp | exact le_top)
  have hc : HasFDerivAt (fun z => α (Complex.exp z))
      ((fderiv ℝ α (Complex.exp w)).comp ((ContinuousLinearMap.mul ℝ ℂ) (Complex.exp w))) w :=
    hdα.hasFDerivAt.comp w he
  exact hc.mul he
end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.Ann
