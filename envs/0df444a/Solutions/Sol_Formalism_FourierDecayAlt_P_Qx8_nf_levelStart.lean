-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Qx8.nf_levelStart
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T01:48:49.949736+00:00
-- url     : https://prove2.me/submissions/5d97a10d-effd-405e-be2b-6a3e3b30d918

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TransferRtt
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexifiedDerivativeCommutator
import Definitions.Def_Formalism_FormalDegreeBessel_FinalWR
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_YangianSpanCharacter_YangianRelationFirst
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstEmbeddingOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrbitalIntegralAeConvergenceContinuity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TwoByOneBlock
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GammaFamilyCommuteGenerators
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_MulIntegralStatement
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RestrictionIrrelevantDoubleLevelOperator
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx8_nf_low_sum
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx8_normal_form_kappa_of_start_vector
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_PC_IsPolyS_id
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx8_coordinate_real
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx8_fn_cancel
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx8_isStart_smul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx8_sgn_sq
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx8_sgn_star


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset MeasureTheory
open scoped ContDiff InnerProductSpace
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Qx8
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Formalism.FourierDecayAlt.M Formalism.FourierDecayAlt.Fr Formalism.FourierDecayAlt.R
variable {P : M.Par} {𝒜 : Type} [Ring 𝒜] [StarRing 𝒜] [Algebra ℂ 𝒜] [StarModule ℂ 𝒜]
namespace Formalism.FourierDecayAlt.P.Qx8
theorem _root_.solution (d : NFData P 𝒜) (hR : d.Rel) (QQ : ℂ → Matrix (Fin 2) (Fin 2) 𝒜) (hQ : ∀ Y, QQ Y = d.QQ Y)
    (hS : Wd.IsStart QQ (qC P)) (hT : ∀ Y Y', Commute (QQ Y 1 0) (QQ Y' 1 0)) (l : ℕ) :
    Fr.IsLevelStart d.L (nfStart d QQ l) := by
  obtain ⟨hstar, hκ, hSS, hshift, -, -⟩ := id hR
  have hzf : ∀ g ∈ zfns d.L, g ∈ d.L.fns := fun g hg => Or.inr hg
  refine ⟨Mx8.isStart_smul QQ (qC P) (sgn P l) (Mx8.sgn_sq P l) (Mx8.sgn_star P l) hS, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_⟩
  · intro Y Y'
    show Commute (sgn P l • QQ Y 1 0) (sgn P l • QQ Y' 1 0)
    exact ((hT Y Y').smul_left _).smul_right _
  · intro Y hY
    have hne : ∀ π, x0 P l π Y ≠ 0 := fun π =>
      mul_ne_zero (pow_ne_zero _ (by norm_num)) (hY π)
    have h1 : ((fun π => x0 P l π Y) * fun π => (x0 P l π Y)⁻¹) = (1 : Ty P → ℂ) := by
      funext π; exact mul_inv_cancel₀ (hne π)
    have h2 : ((fun π => (x0 P l π Y)⁻¹) * fun π => x0 P l π Y) = (1 : Ty P → ℂ) := by
      funext π; exact inv_mul_cancel₀ (hne π)
    refine ⟨?_, ?_⟩
    · show (d.κ fun π => x0 P l π Y) * (d.κ fun π => (x0 P l π Y)⁻¹) = 1
      rw [← map_mul, h1, map_one]
    · show (d.κ fun π => (x0 P l π Y)⁻¹) * (d.κ fun π => x0 P l π Y) = 1
      rw [← map_mul, h2, map_one]
  · intro Y Y'
    show _ * _ = _ * _
    simp only [nfStart]
    rw [← map_mul, ← map_mul, mul_comm]
  · intro Y g hg
    exact hκ _ g (Or.inl (hzf g hg))
  · intro Y
    exact hκ _ _ (Or.inr (by simp))
  · intro Y hY
    show star (d.κ fun π => x0 P l π Y) = d.κ fun π => x0 P l π Y
    rw [hstar]
    congr 1
    funext π
    exact Mx8.coordinate_real P l π Y hY
  · intro Y g hg
    have h1 : Commute d.L.ζ g := d.L.fns_comm _ (Or.inr (by simp)) g (Or.inr hg)
    have h2 : Commute d.L.ζbi g := d.L.fns_comm _ (Or.inr (by simp)) g (Or.inr hg)
    have h3 : Commute (∑ j ∈ Icc 1 (P.k - 1), (d.κ fun π => (Y + (rho P π j : ℂ))⁻¹) * d.SS j) g :=
      Commute.sum_left _ _ _ fun j _ =>
        (hκ _ g (Or.inl (hzf g hg))).mul_left (hSS j g (Or.inl (Or.inl (hzf g hg))))
    exact (h1.mul_left h2).mul_left h3
  · intro Y
    show sgn P l • QQ Y 1 1 = d.L.GG * d.κ (fun π => x0 P l π Y)
    rw [normal_form_kappa_of_start_vector, mul_smul_comm, hQ]
    rfl
  · intro Y hY
    have hcan := Mx8.fn_cancel d.L
    have hgi := d.L.GG_GGi
    have hcx : d.L.GG * d.x Y = d.x Y * d.L.GG := ((hκ _ d.L.GG (Or.inl (Or.inr (by simp)))).eq).symm
    show sgn P l • QQ Y 1 0 = d.L.GG * (d.κ fun π => x0 P l π Y) * (d.L.l0 Y + d.L.ζb * d.L.ζi * d.L.GGi *
      (d.L.ζ * d.L.ζbi * ∑ j ∈ Icc 1 (P.k - 1), (d.κ fun π => (Y + (rho P π j : ℂ))⁻¹) * d.SS j))
    have e : QQ Y 1 0 = d.L.GG * d.x Y * d.L.l0 Y + d.weightedSumBis Y := by rw [hQ]; rfl
    rw [e, normal_form_kappa_of_start_vector, ← nf_low_sum d hR Y hY, ← mul_assoc _ (d.L.ζ * d.L.ζbi), hcan,
      mul_smul_comm, smul_mul_assoc, mul_add]
    congr 2
    rw [hcx, mul_assoc, ← mul_assoc d.L.GG, hgi, one_mul]
end Formalism.FourierDecayAlt.P.Qx8
