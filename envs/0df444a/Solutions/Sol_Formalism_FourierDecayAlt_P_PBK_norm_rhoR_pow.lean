-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.PBK.norm_rhoR_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T07:13:38.532176+00:00
-- url     : https://prove2.me/submissions/cac34374-e4bd-4b10-b2c2-a5bedc990cc6

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TendstoSmulCocompact
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LastBlockDecay
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralNormCvecSq
import Theorems.Thm_Formalism_FourierDecayAlt_P_PBK_rhoR_pow_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.PBK
open Formalism.FourierDecayAlt Finset Filter Topology MeasureTheory
open scoped ComplexConjugate InnerProductSpace
noncomputable section
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
namespace Formalism.FourierDecayAlt.P.PBK
theorem _root_.solution {s : ℕ} (hs : s ≠ 0) (σ x : ℂ) :
    ‖rhoR s σ x‖ ^ s = ‖x ^ (s - 1) / (x + σ) ^ (s - 1)‖ := by
  rw [← norm_pow, rhoR_pow_eq hs]
end Formalism.FourierDecayAlt.P.PBK
