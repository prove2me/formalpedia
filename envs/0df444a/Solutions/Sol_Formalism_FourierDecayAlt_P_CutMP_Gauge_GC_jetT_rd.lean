-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.jetT_rd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T08:03:47.908335+00:00
-- url     : https://prove2.me/submissions/51107a45-2009-4691-9be6-20538475df18

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutGCoreGTCLRadTCut
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumDualVectorEqZeta
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutGCoreGTCLRadTJet
import Theorems.Thm_Formalism_FourierDecayAlt_P_CutMP_Gauge_GC_jetT_le
import Theorems.Thm_Formalism_FourierDecayAlt_P_CutMP_Gauge_GC_jetT_gen
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_hasDeriv_ext


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt
open scoped ContDiff
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CutMP Formalism.FourierDecayAlt.P.CutMP.Gauge Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
theorem _root_.solution {N : ℕ} {f : Q.Mx k r → E} {g₀ X : Q.Mx k r}
    (hX : Q.inLieLev k r (Fin.last r) X) (h : ZJ k r (N + 1) f g₀) : ZJ k r N (RdV X f) g₀ := by
  obtain ⟨U, F, hU, hgU, hF, hfF, hv⟩ := h
  let L : Q.Mx k r →L[ℝ] Q.Mx k r := (LinearMap.mulRight ℝ X).toContinuousLinearMap
  have hL : ∀ x, L x = x * X := fun x => rfl
  have hG := jetT_gen hU hgU hF L N hv
  refine ⟨U, fun x => fderiv ℝ F x (L x), hU, hgU, hG.1, ?_, hG.2⟩
  intro g hg hgl
  have hd : DifferentiableAt ℝ F g :=
    (hF.contDiffAt (hU.mem_nhds hg)).differentiableAt (by simpa using jetT_le 1)
  show RdV X f g = fderiv ℝ F g (L g)
  rw [hL]
  exact (Formalism.FourierDecayAlt.P.Qx2.hasDeriv_ext hU hg hgl hX hd hfF).deriv
end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
