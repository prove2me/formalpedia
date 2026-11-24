-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.JCx1.needs.orbJ_cutF
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T18:31:06.037232+00:00
-- url     : https://prove2.me/submissions/156cc773-5bcb-4c52-a922-676147620bf9

import Definitions.Def_Formalism_HermitianCurvature_StatementJC
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FrameIntegralJacobian
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BlockEstimatesSumForm
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BigCellZetaMinors
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelSizesJointMean
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TheoremPIntegralOfPlaces
import Theorems.Thm_Formalism_FourierDecayAlt_P_JCx1_needs_gf_sgs
import Theorems.Thm_Formalism_FourierDecayAlt_P_JCx1_needs_orbJ_smul_of_ae
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x3_haarW


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt
open Formalism.FourierDecayAlt
open Formalism.FourierDecayAlt Filter Topology MeasureTheory NumberField
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.JCx1 Formalism.FourierDecayAlt.P.JCx1.needs
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
namespace Formalism.FourierDecayAlt.P.JCx1.needs
theorem _root_.solution (Bs : RealPlaceData k r Wp Wq) (γ : Mat k r) (μR : Measure (Mt k r))
    (χ : ℝ → ℝ) (f : Mat k r → (Wq →L[ℂ] Wp)) (ε : ℝ) :
    D.orbJ Bs γ μR (D.cutF Bs χ f ε) = ((χ (Gf k r Bs.z Bs.z' γ / ε) : ℝ) : ℂ) • D.orbJ Bs γ μR f := by
  have hfin : ∀ (U : Set (Mat k r)) (μ : Measure (Mt k r)), IsHaarOn U μ → SFinite μ := by
    intro U μ h
    haveI : IsFiniteMeasureOnCompacts μ := ⟨h.finite_compact⟩
    infer_instance
  haveI := hfin _ _ Bs.haarW
  haveI := hfin _ _ Bs.haarN
  haveI := hfin _ _ Bs.haarW'
  have hW : ∀ᵐ x ∂Bs.μW, Matrix.of x ∈ UWset k r Bs.z := ae_iff.2 Bs.haarW.conc
  have hN : ∀ᵐ x ∂Bs.μN, Matrix.of x ∈ Nset k r := ae_iff.2 Bs.haarN.conc
  have hW' : ∀ᵐ x ∂Bs.μW', Matrix.of x ∈ UWset k r Bs.z' := ae_iff.2 Bs.haarW'.conc
  have a1 : ∀ᵐ p ∂((Bs.μW.prod Bs.μN).prod (Bs.μW'.prod Bs.μN)), Matrix.of p.1.1 ∈ UWset k r Bs.z :=
    (Measure.quasiMeasurePreserving_fst (μ := Bs.μW.prod Bs.μN) (ν := Bs.μW'.prod Bs.μN)).ae
      ((Measure.quasiMeasurePreserving_fst (μ := Bs.μW) (ν := Bs.μN)).ae hW)
  have a2 : ∀ᵐ p ∂((Bs.μW.prod Bs.μN).prod (Bs.μW'.prod Bs.μN)), Matrix.of p.1.2 ∈ Nset k r :=
    (Measure.quasiMeasurePreserving_fst (μ := Bs.μW.prod Bs.μN) (ν := Bs.μW'.prod Bs.μN)).ae
      ((Measure.quasiMeasurePreserving_snd (μ := Bs.μW) (ν := Bs.μN)).ae hN)
  have a3 : ∀ᵐ p ∂((Bs.μW.prod Bs.μN).prod (Bs.μW'.prod Bs.μN)), Matrix.of p.2.1 ∈ UWset k r Bs.z' :=
    (Measure.quasiMeasurePreserving_snd (μ := Bs.μW.prod Bs.μN) (ν := Bs.μW'.prod Bs.μN)).ae
      ((Measure.quasiMeasurePreserving_fst (μ := Bs.μW') (ν := Bs.μN)).ae hW')
  have a4 : ∀ᵐ p ∂((Bs.μW.prod Bs.μN).prod (Bs.μW'.prod Bs.μN)), Matrix.of p.2.2 ∈ Nset k r :=
    (Measure.quasiMeasurePreserving_snd (μ := Bs.μW.prod Bs.μN) (ν := Bs.μW'.prod Bs.μN)).ae
      ((Measure.quasiMeasurePreserving_snd (μ := Bs.μW') (ν := Bs.μN)).ae hN)
  have hae : ∀ᵐ p ∂Bs.μSS, Bs.inSS p := by
    unfold RealPlaceData.μSS
    filter_upwards [a1, a2, a3, a4] with p h1 h2 h3 h4
    exact ⟨h1, h2, h3, h4⟩
  apply orbJ_smul_of_ae
  filter_upwards [hae] with p hp
  simp only [D.orbIntegrand, B.rho, D.cutF, gf_sgs Bs hp γ]
  rw [ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul, smul_comm]
end Formalism.FourierDecayAlt.P.JCx1.needs
