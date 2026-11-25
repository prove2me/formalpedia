-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.Ann.contDiffAt_br
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T07:32:09.428061+00:00
-- url     : https://prove2.me/submissions/de8ec16f-5143-4605-8744-40f148f518b6

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ThShiftInt
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NeZeroOfAn
import Theorems.Thm_Formalism_FourierDecayAlt_P_CutMP_Gauge_GC_Ann_isOpen_brD
import Theorems.Thm_Formalism_FourierDecayAlt_P_CutMP_Gauge_GC_Ann_hasDerivAt_br

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
theorem _root_.solution (s : Bool) {ζ : ℂ} (hs : ζ ∈ brD s) : ContDiffAt ℂ ((⊤ : ℕ∞) : WithTop ℕ∞) (br s) ζ := by
  have hd : DifferentiableOn ℂ (br s) (brD s) := fun z hz =>
    (hasDerivAt_br s hz).differentiableAt.differentiableWithinAt
  exact (hd.contDiffOn (isOpen_brD s)).contDiffAt ((isOpen_brD s).mem_nhds hs)
end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.Ann
