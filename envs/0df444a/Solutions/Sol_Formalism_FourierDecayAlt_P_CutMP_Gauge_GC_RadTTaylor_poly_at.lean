-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.RadTTaylor.poly_at
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T07:36:55.720981+00:00
-- url     : https://prove2.me/submissions/b57cbbbb-d915-4f64-a1da-d7b8ce5f2ef3

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutGCoreGTCLRadTCut
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutGCoreGTCLRadTTaylor
import Theorems.Thm_Formalism_FourierDecayAlt_P_CutMP_Gauge_GC_RadTTaylor_poly_hom

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped ContDiff
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CutMP Formalism.FourierDecayAlt.P.CutMP.Gauge Formalism.FourierDecayAlt.P.CutMP.Gauge.GC Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.RadTTaylor
noncomputable section
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W]
namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.RadTTaylor
theorem _root_.solution {j i : ℕ} (m : ContinuousMultilinearMap ℝ (fun _ : Fin j => E) W) (a : E) (v : Fin i → E) :
    iteratedFDeriv ℝ i (fun ζ => m (fun _ => ζ - a)) a v =
      if h : i = j then ∑ σ : Equiv.Perm (Fin j), m (fun k => (v ∘ Fin.cast h.symm) (σ k)) else 0 := by
  by_cases h : i = j
  · subst h
    rw [dif_pos rfl, iteratedFDeriv_comp_sub (f := fun ζ => m fun _ => ζ), sub_self,
      ContinuousMultilinearMap.iteratedFDeriv_comp_diagonal]
    rfl
  · rw [dif_neg h, iteratedFDeriv_comp_sub (f := fun ζ => m fun _ => ζ), sub_self, poly_hom h m]
    rfl
end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.RadTTaylor
