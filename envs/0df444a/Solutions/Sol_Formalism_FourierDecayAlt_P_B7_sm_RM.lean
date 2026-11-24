-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B7.sm_RM
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T17:17:40.834849+00:00
-- url     : https://prove2.me/submissions/5b6704af-f8f8-4814-993d-86aa156cd1b5

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralZeroFrequencyInvariant
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdjointnessPolynomiallyBounded
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_FormalDegreeBessel_FinalBF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrbitalIntegralAeConvergenceContinuity
import Theorems.Thm_Formalism_FourierDecayAlt_P_B7_measurable_invM
import Theorems.Thm_Formalism_FourierDecayAlt_P_B7_sm_piM
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_B7_sm_piM__11e3047c332f
import Theorems.Thm_Formalism_FourierDecayAlt_P_B7_sm_FM
import Theorems.Thm_Formalism_FourierDecayAlt_P_B7_measurable_sgsM

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
attribute [local instance] sfG sfW sfN sfW' sfSS
attribute [local instance] properFD
namespace Formalism.FourierDecayAlt.P.B7
theorem _root_.solution (D : RealPlaceData k r Wp Wq) {F : Mat k r → (Wq →L[ℂ] Wp)} (hF : ContinuousOn F (GV k r)) :
    StronglyMeasurable fun a : SS k r × Mt k r => RM D F a.1 a.2 := by
  have f1 : StronglyMeasurable fun a : SS k r × Mt k r => piM D a.1.1.1 :=
    (sm_piM D).comp_measurable measurable_fst.fst.fst
  have f2 : StronglyMeasurable fun a : SS k r × Mt k r => FM F (sgsM a.1 a.2) :=
    (sm_FM hF).comp_measurable measurable_sgsM
  have f3 : StronglyMeasurable fun a : SS k r × Mt k r => piM' D (invM a.1.2.1) :=
    (sm_piM' D).comp_measurable (measurable_invM.comp measurable_fst.snd.fst)
  show StronglyMeasurable fun a : SS k r × Mt k r => (piM D a.1.1.1).comp ((FM F (sgsM a.1 a.2)).comp (piM' D (invM a.1.2.1)))
  first
    | exact isBoundedBilinearMap_comp.continuous.comp_stronglyMeasurable
        (f1.prodMk (isBoundedBilinearMap_comp.continuous.comp_stronglyMeasurable (f2.prodMk f3)))
    | exact isBoundedBilinearMap_comp.continuous.comp_stronglyMeasurable
        (f1.prod_mk (isBoundedBilinearMap_comp.continuous.comp_stronglyMeasurable (f2.prod_mk f3)))
end Formalism.FourierDecayAlt.P.B7
