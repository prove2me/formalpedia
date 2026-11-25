-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.gTCCurv_of_cut
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T07:43:36.463088+00:00
-- url     : https://prove2.me/submissions/71287308-d3b5-48b3-a33f-95af1cf2a784

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_cut_GCore_GTConnCut
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutGCoreGTCHolCut
import Theorems.Thm_Formalism_FourierDecayAlt_P_CutMP_Gauge_GC_ann_isOpen
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
theorem _root_.solution : GTCCurvOfCut := by
  intro hRef hPR hU hCP hPc Wp Wq _ _ _ _ _ _ P Bs X d hyp e he hk A B hAB hConn ρ ζ hζ
  obtain ⟨A0, u, hA0s, hu, hws, hcurv, -, hA⟩ :=
    gauge_rel hRef hPR hU hCP Wp Wq P Bs X d hyp e he hk A B hAB hConn
  have hTT := tt_nonneg_of_hyp hyp
  have hnhds : Ann P ∈ nhds ζ := (ann_isOpen P).mem_nhds hζ
  have hev : (fun w => modA P ρ w - A ρ w) =ᶠ[nhds ζ]
      fun w => (modA P ρ w - A0 ρ w) - star (u ρ w) * NF.dZ (u ρ) w := by
    filter_upwards [hnhds] with w hw
    rw [hA ρ w hw]
    ring
  have hfd : DifferentiableAt ℝ (fun w => modA P ρ w - A0 ρ w) ζ :=
    (((modA_smooth P ρ hTT).sub (hA0s ρ)).differentiableOn (by simp)).differentiableAt hnhds
  have hgd : DifferentiableAt ℝ (fun w => star (u ρ w) * NF.dZ (u ρ) w) ζ :=
    ((hws ρ).differentiableOn (by simp)).differentiableAt hnhds
  have hder : fderiv ℝ (fun w => modA P ρ w - A ρ w) ζ =
      fderiv ℝ (fun w => modA P ρ w - A0 ρ w) ζ - fderiv ℝ (fun w => star (u ρ w) * NF.dZ (u ρ) w) ζ := by
    exact hev.fderiv_eq.trans (hfd.hasFDerivAt.sub hgd.hasFDerivAt).fderiv
  have h1 := hcurv ρ ζ hζ
  have h2 := hPc P.TT (u ρ) (hu ρ).1 (hu ρ).2 ζ hζ
  unfold NF.dZb at h1 h2 ⊢
  rw [hder, ContinuousLinearMap.sub_apply, ContinuousLinearMap.sub_apply]
  have key : ∀ a b c d : ℂ, (1 / 2 : ℂ) * ((a - b) + Complex.I * (c - d)) =
      (1 / 2 : ℂ) * (a + Complex.I * c) - (1 / 2 : ℂ) * (b + Complex.I * d) := by
    intros; ring
  rw [key, Complex.sub_re, h1, h2, sub_zero]
end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
