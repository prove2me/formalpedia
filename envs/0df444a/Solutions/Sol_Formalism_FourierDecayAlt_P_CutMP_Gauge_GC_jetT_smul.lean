-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.jetT_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T07:16:13.906203+00:00
-- url     : https://prove2.me/submissions/fd5312e4-7b7c-4773-a01d-0819c98a9f49

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutGCoreGTCLRadTCut
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumDualVectorEqZeta
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutGCoreGTCLRadTJet
import Theorems.Thm_Formalism_FourierDecayAlt_P_CutMP_Gauge_GC_jetT_le

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
theorem _root_.solution {N : ℕ} (c : ℂ) {f : Q.Mx k r → E} {g₀ : Q.Mx k r} (h : ZJ k r N f g₀) :
    ZJ k r N (fun x => c • f x) g₀ := by
  obtain ⟨U, F, hU, hgU, hF, hfF, hv⟩ := h
  refine ⟨U, fun x => c • F x, hU, hgU, hF.const_smul c, ?_, ?_⟩
  · intro g hg hgl
    simp only [hfF g hg hgl]
  · intro j hj
    show iteratedFDeriv ℝ j (c • F) g₀ = 0
    rw [← iteratedFDerivWithin_of_isOpen j hU hgU,
      iteratedFDerivWithin_const_smul_apply ((hF g₀ hgU).of_le (jetT_le j)) hU.uniqueDiffOn hgU,
      iteratedFDerivWithin_of_isOpen j hU hgU, hv j hj, smul_zero]
end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
