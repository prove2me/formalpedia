-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.gTCHol_of_cut
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:06:12.48846+00:00
-- url     : https://prove2.me/submissions/9652252a-c2e0-48dd-be76-5ca4e255c114

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_cut_GCore_GTConnCut
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutGCoreGTCHolCut
import Theorems.Thm_Formalism_FourierDecayAlt_P_CutMP_Gauge_GC_sphere_sub_ann
import Theorems.Thm_Formalism_FourierDecayAlt_P_CutMP_Gauge_GC_tt_nonneg_of_hyp
import Theorems.Thm_Formalism_FourierDecayAlt_P_CutMP_Gauge_GC_gauge_rel
import Theorems.Thm_Formalism_FourierDecayAlt_P_CutMP_Gauge_GC_modA_smooth


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CutMP Formalism.FourierDecayAlt.P.CutMP.Gauge Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
noncomputable section
namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
theorem _root_.solution : GTCHolOfCut := by
  intro hRef hPR hU hCP hPh Wp Wq _ _ _ _ _ _ P Bs X d hyp e he hk A B hAB hConn ρ R hR0 hR
  obtain ⟨A0, u, hA0s, hu, hws, -, hhol, hA⟩ :=
    gauge_rel hRef hPR hU hCP Wp Wq P Bs X d hyp e he hk A B hAB hConn
  have hTT := tt_nonneg_of_hyp hyp
  obtain ⟨n1, hn1⟩ := hhol ρ R hR0 hR
  obtain ⟨n2, hn2⟩ := hPh P.TT (u ρ) (hu ρ).1 (hu ρ).2 R hR0 hR
  have hsph := sphere_sub_ann P hR0 hR
  have hf : CircleIntegrable (fun w => modA P ρ w - A0 ρ w) 0 R :=
    ContinuousOn.circleIntegrable hR0.le (((modA_smooth P ρ hTT).sub (hA0s ρ)).continuousOn.mono hsph)
  have hg : CircleIntegrable (fun w => star (u ρ w) * NF.dZ (u ρ) w) 0 R :=
    ContinuousOn.circleIntegrable hR0.le ((hws ρ).continuousOn.mono hsph)
  have heq : (∮ w in C(0, R), modA P ρ w - A ρ w) =
      ∮ w in C(0, R), (modA P ρ w - A0 ρ w) - star (u ρ w) * NF.dZ (u ρ) w := by
    apply circleIntegral.integral_congr hR0.le
    intro w hw
    try dsimp only
    rw [hA ρ w (hsph hw)]
    ring
  refine ⟨n1 - n2, ?_⟩
  rw [heq, circleIntegral.integral_sub hf hg, Complex.sub_im, hn1, hn2]
  push_cast
  ring
end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
