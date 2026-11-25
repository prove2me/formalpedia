-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.PBK.cvec_eq_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T07:00:18.449853+00:00
-- url     : https://prove2.me/submissions/1c5e2885-6393-4e4a-95e4-15b0730fda64

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TendstoSmulCocompact
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LastBlockDecay
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralNormCvecSq

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
theorem _root_.solution (s : ℕ) (F : ℂ → ℂ → H) (x : ℂ) :
    cvec s F x = fun c => (((‖x‖ ^ (s - 1))⁻¹ : ℝ) : ℂ) • F x ((x ^ (s - 1))⁻¹ * c) := by
  funext c
  simp only [cvec, div_eq_inv_mul]
end Formalism.FourierDecayAlt.P.PBK
