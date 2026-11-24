-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S3dx4.triple_integrand_measurable
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:29:07.729803+00:00
-- url     : https://prove2.me/submissions/4bcb90bf-2c77-4c2a-aa4c-9d2ff7c8f5d5

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InnerBound
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TripleIntegrandMeasurable
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3dx4_mt_cont


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal NNReal
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.S3dx4
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.P.S3dx4
theorem _root_.solution {α : Type*} [TopologicalSpace α] [MeasurableSpace α] [OpensMeasurableSpace α]
    {e1 e2 : Mx k r → ℂ} (he1 : Continuous e1) (he2 : Continuous e2) (γi : Mx k r)
    {X : α → Formalism.QuantumDeterminants.Mt k r} {Pp Qq : α → Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r}
    (hX : Continuous X) (hP : Continuous Pp) (hQ : Continuous Qq) :
    Measurable (fun t => Phi3 e1 e2 γi (X t) (Pp t) (Qq t)) := by
  unfold Phi3
  exact ((he1.comp (((mt_cont.comp hP.fst).matrix_mul (mt_cont.comp hP.snd)).matrix_mul
    (mt_cont.comp hX))).enorm.measurable).mul
    ((he2.comp (((mt_cont.comp hQ.fst).matrix_mul (mt_cont.comp hQ.snd)).matrix_mul
    (continuous_const.matrix_mul (mt_cont.comp hX)))).enorm.measurable)
end Formalism.FourierDecayAlt.P.S3dx4
