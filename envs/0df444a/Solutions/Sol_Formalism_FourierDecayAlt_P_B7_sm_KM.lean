-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B7.sm_KM
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T17:36:08.108999+00:00
-- url     : https://prove2.me/submissions/f8613d6c-ab0e-4a3d-86dd-136f4762d474

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralZeroFrequencyInvariant
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdjointnessPolynomiallyBounded
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_FormalDegreeBessel_FinalBF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrbitalIntegralAeConvergenceContinuity
import Theorems.Thm_Formalism_FourierDecayAlt_P_B7_sm_FM
import Theorems.Thm_Formalism_FourierDecayAlt_P_B7_sm_RM

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B7
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
attribute [local instance] sfG sfW sfN sfW' sfSS properFD
namespace Formalism.FourierDecayAlt.P.B7
theorem _root_.solution (D : RealPlaceData k r Wp Wq) {F : Mat k r → (Wq →L[ℂ] Wp)} (hF : ContinuousOn F (GV k r)) :
    StronglyMeasurable fun a : SS k r × Mt k r => KM D F a.1 a.2 := by
  have hv : Continuous (hsVec : (Wq →L[ℂ] Wp) → PiLp 2 (fun _ : Fin (Module.finrank ℂ Wq) => Wp)) :=
    (hsL (Wp := Wp) (Wq := Wq)).continuous
  have hc : Continuous fun x : (Wq →L[ℂ] Wp) × (Wq →L[ℂ] Wp) => inner ℂ (hsVec x.2) (hsVec x.1) :=
    (hv.comp continuous_snd).inner (hv.comp continuous_fst)
  have hp : StronglyMeasurable fun a : SS k r × Mt k r => (RM D F a.1 a.2, FM F a.2) := by
    first
      | exact (sm_RM D hF).prodMk ((sm_FM hF).comp_measurable measurable_snd)
      | exact (sm_RM D hF).prod_mk ((sm_FM hF).comp_measurable measurable_snd)
  exact hc.comp_stronglyMeasurable hp
end Formalism.FourierDecayAlt.P.B7
