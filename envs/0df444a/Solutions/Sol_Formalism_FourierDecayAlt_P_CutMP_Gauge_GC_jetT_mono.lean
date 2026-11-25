-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.jetT_mono
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T06:58:54.756813+00:00
-- url     : https://prove2.me/submissions/77c523e0-c259-4021-895c-8bd3b56023ec

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutGCoreGTCLRadTCut
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumDualVectorEqZeta
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutGCoreGTCLRadTJet

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
theorem _root_.solution {N M : ℕ} (hMN : M ≤ N) {f : Q.Mx k r → E} {g₀ : Q.Mx k r} (h : ZJ k r N f g₀) :
    ZJ k r M f g₀ := by
  obtain ⟨U, F, hU, hgU, hF, hfF, hv⟩ := h
  exact ⟨U, F, hU, hgU, hF, hfF, fun j hj => hv j (hj.trans hMN)⟩
end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
