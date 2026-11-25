-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.CutBP.ccleQ_mono_c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T06:59:19.523009+00:00
-- url     : https://prove2.me/submissions/ec5e4d7c-b641-4c08-80e2-b3becc9969e8

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutJDCCLower
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutNFApxDomThQ

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity
open scoped ContDiff
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CutBP
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
noncomputable section
namespace Formalism.FourierDecayAlt.P.CutBP
theorem _root_.solution {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {A : ℝ} {m : ℕ}
    {F : B.Mat k r → E} {b b' : ℝ} (h : B.CCle A m F b) (hb : b ≤ b') : B.CCle A m F b' := ⟨h.1, fun u v hu hv hl g hg => (h.2 u v hu hv hl g hg).trans hb⟩
end Formalism.FourierDecayAlt.P.CutBP
