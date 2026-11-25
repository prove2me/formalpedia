-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B7.jc_aesm_J
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T03:42:45.350831+00:00
-- url     : https://prove2.me/submissions/a577bc2e-dcef-45c7-8d06-cffb5d106b6a

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralZeroFrequencyInvariant
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdjointnessPolynomiallyBounded
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_FormalDegreeBessel_FinalBF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrbitalIntegralAeConvergenceContinuity
import Theorems.Thm_Formalism_FourierDecayAlt_P_B7_measurable_invM
import Theorems.Thm_Formalism_FourierDecayAlt_P_B7_measurable_gqM
import Theorems.Thm_Formalism_FourierDecayAlt_P_B7_ae_mem_good_set_restrict
import Theorems.Thm_Formalism_FourierDecayAlt_P_B7_sm_piM
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_B7_sm_piM__11e3047c332f
import Theorems.Thm_Formalism_FourierDecayAlt_P_B7_sm_FM
import Theorems.Thm_Formalism_FourierDecayAlt_P_B7_meas_mulM
import Theorems.Thm_Formalism_FourierDecayAlt_P_B7_sgsM_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_B7_measurable_xi
import Theorems.Thm_Formalism_FourierDecayAlt_P_B7_JM_eq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal
noncomputable section
namespace Formalism.FourierDecayAlt.P.B7
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
section common
variable {k r : ℕ}
end common
section setting
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
attribute [local instance] sfG sfW sfN sfW'
attribute [local instance] sfSS
end setting
section fd
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
attribute [local instance] sfG sfW sfN sfW' sfSS
attribute [local instance] properFD
end fd
section dil
variable {k r : ℕ}
variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
end dil
section jc
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
attribute [local instance] sfG sfW sfN sfW' sfSS properFD
private theorem stronglyMeasurable_rm_comp (D : RealPlaceData k r Wp Wq) {F : Mat k r → (Wq →L[ℂ] Wp)} (hF : ContinuousOn F (GV k r))
    {α : Type*} [MeasurableSpace α] {φ : α → SS k r} {ψ : α → Mt k r} (hφ : Measurable φ) (hψ : Measurable ψ) :
    StronglyMeasurable fun a => RM D F (φ a) (ψ a) := by
  have f1 : StronglyMeasurable fun a => piM D (φ a).1.1 := (sm_piM D).comp_measurable hφ.fst.fst
  have hs : Measurable fun a => sgsM (φ a) (ψ a) := by
    have e : (fun a => sgsM (φ a) (ψ a)) = fun a =>
        mulM (mulM (mulM (mulM (invM (φ a).1.1) (invM (φ a).1.2)) (ψ a)) (φ a).2.2) (φ a).2.1 :=
      funext fun a => sgsM_eq (φ a) (ψ a)
    rw [e]
    exact meas_mulM (meas_mulM (meas_mulM (meas_mulM (measurable_invM.comp hφ.fst.fst)
      (measurable_invM.comp hφ.fst.snd)) hψ) hφ.snd.snd) hφ.snd.fst
  have f2 : StronglyMeasurable fun a => FM F (sgsM (φ a) (ψ a)) := (sm_FM hF).comp_measurable hs
  have f3 : StronglyMeasurable fun a => piM' D (invM (φ a).2.1) :=
    (sm_piM' D).comp_measurable (measurable_invM.comp hφ.snd.fst)
  show StronglyMeasurable fun a => (piM D (φ a).1.1).comp ((FM F (sgsM (φ a) (ψ a))).comp (piM' D (invM (φ a).2.1)))
  first
    | exact isBoundedBilinearMap_comp.continuous.comp_stronglyMeasurable
        (f1.prodMk (isBoundedBilinearMap_comp.continuous.comp_stronglyMeasurable (f2.prodMk f3)))
    | exact isBoundedBilinearMap_comp.continuous.comp_stronglyMeasurable
        (f1.prod_mk (isBoundedBilinearMap_comp.continuous.comp_stronglyMeasurable (f2.prod_mk f3)))
end jc
section alg
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
attribute [local instance] sfG sfW sfN sfW' sfSS properFD
end alg
section u12
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
attribute [local instance] sfG sfW sfN sfW' sfSS properFD
end u12
section abstractFubini
end abstractFubini
section u3
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
attribute [local instance] sfG sfW sfN sfW' sfSS properFD
end u3
section abstractFinal
end abstractFinal
section u4
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
attribute [local instance] sfG sfW sfN sfW' sfSS properFD
attribute [local instance] sfNu
end u4
end Formalism.FourierDecayAlt.P.B7
namespace Formalism.FourierDecayAlt.P
end Formalism.FourierDecayAlt.P
end
end

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
theorem _root_.solution (D : RealPlaceData k r Wp Wq) {F : Mat k r → (Wq →L[ℂ] Wp)} (hF : ContinuousOn F (GV k r))
    (τ : ℝ × ℝ) : AEStronglyMeasurable (fun q => Jtau D τ F (gq D q)) (volume.restrict (Qset D)) := by
  have hx : Measurable fun b : ((Fin r → ℂ) × ℂ) × SS k r => xiTau D τ b.2 := by
    first
      | exact (measurable_xi D).comp (measurable_const.prodMk measurable_snd)
      | exact (measurable_xi D).comp (measurable_const.prod_mk measurable_snd)
  have hb : StronglyMeasurable fun b : ((Fin r → ℂ) × ℂ) × SS k r => xiTau D τ b.2 • RM D F b.2 (gqM D b.1) :=
    hx.stronglyMeasurable.smul (stronglyMeasurable_rm_comp D hF measurable_snd ((measurable_gqM D).comp measurable_fst))
  have hs : StronglyMeasurable fun q => JM D F τ q := hb.integral_prod_right'
  refine hs.aestronglyMeasurable.congr ?_
  filter_upwards [ae_mem_good_set_restrict D] with q hq
  exact JM_eq D F τ hq
end Formalism.FourierDecayAlt.P.B7
