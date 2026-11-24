-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B7.sm_A
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T16:57:53.568902+00:00
-- url     : https://prove2.me/submissions/6f97b0e5-1034-4260-9614-f1534cbe64ed

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralZeroFrequencyInvariant
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdjointnessPolynomiallyBounded
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_FormalDegreeBessel_FinalBF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrbitalIntegralAeConvergenceContinuity
import Theorems.Thm_Formalism_FourierDecayAlt_P_B7_measurable_invM
import Theorems.Thm_Formalism_FourierDecayAlt_P_B7_measurable_gqM
import Theorems.Thm_Formalism_FourierDecayAlt_P_B7_sm_piM
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_B7_sm_piM__11e3047c332f
import Theorems.Thm_Formalism_FourierDecayAlt_P_B7_sm_FM
import Theorems.Thm_Formalism_FourierDecayAlt_P_B7_meas_mulM
import Theorems.Thm_Formalism_FourierDecayAlt_P_B7_sgsM_eq

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
set_option maxHeartbeats 800000
namespace Formalism.FourierDecayAlt.P.B7
theorem _root_.solution (D : RealPlaceData k r Wp Wq) {F : Mat k r → (Wq →L[ℂ] Wp)} (hF : ContinuousOn F (GV k r)) :
    StronglyMeasurable fun b : ((ℝ × ℝ) × ((Fin r → ℂ) × ℂ)) × SS k r => RM D F b.2 (gqM D b.1.2) := by
  have hm : Measurable fun b : ((ℝ × ℝ) × ((Fin r → ℂ) × ℂ)) × SS k r => gqM D b.1.2 :=
    (measurable_gqM D).comp measurable_fst.snd
  have f1 : StronglyMeasurable fun b : ((ℝ × ℝ) × ((Fin r → ℂ) × ℂ)) × SS k r => piM D b.2.1.1 :=
    (sm_piM D).comp_measurable measurable_snd.fst.fst
  have hs : Measurable fun b : ((ℝ × ℝ) × ((Fin r → ℂ) × ℂ)) × SS k r => sgsM b.2 (gqM D b.1.2) := by
    have e : (fun b : ((ℝ × ℝ) × ((Fin r → ℂ) × ℂ)) × SS k r => sgsM b.2 (gqM D b.1.2)) = fun b =>
        mulM (mulM (mulM (mulM (invM b.2.1.1) (invM b.2.1.2)) (gqM D b.1.2)) b.2.2.2) b.2.2.1 :=
      funext fun b => sgsM_eq b.2 (gqM D b.1.2)
    rw [e]
    exact meas_mulM (meas_mulM (meas_mulM (meas_mulM (measurable_invM.comp measurable_snd.fst.fst)
      (measurable_invM.comp measurable_snd.fst.snd)) hm) measurable_snd.snd.snd) measurable_snd.snd.fst
  have f2 : StronglyMeasurable fun b : ((ℝ × ℝ) × ((Fin r → ℂ) × ℂ)) × SS k r => FM F (sgsM b.2 (gqM D b.1.2)) :=
    (sm_FM hF).comp_measurable hs
  have f3 : StronglyMeasurable fun b : ((ℝ × ℝ) × ((Fin r → ℂ) × ℂ)) × SS k r => piM' D (invM b.2.2.1) :=
    (sm_piM' D).comp_measurable (measurable_invM.comp measurable_snd.snd.fst)
  show StronglyMeasurable fun b : ((ℝ × ℝ) × ((Fin r → ℂ) × ℂ)) × SS k r =>
    (piM D b.2.1.1).comp ((FM F (sgsM b.2 (gqM D b.1.2))).comp (piM' D (invM b.2.2.1)))
  first
    | exact isBoundedBilinearMap_comp.continuous.comp_stronglyMeasurable
        (f1.prodMk (isBoundedBilinearMap_comp.continuous.comp_stronglyMeasurable (f2.prodMk f3)))
    | exact isBoundedBilinearMap_comp.continuous.comp_stronglyMeasurable
        (f1.prod_mk (isBoundedBilinearMap_comp.continuous.comp_stronglyMeasurable (f2.prod_mk f3)))
end Formalism.FourierDecayAlt.P.B7
