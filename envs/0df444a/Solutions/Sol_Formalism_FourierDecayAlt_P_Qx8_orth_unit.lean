-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Qx8.orth_unit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T02:10:12.493748+00:00
-- url     : https://prove2.me/submissions/03fd17a8-54a2-4b5b-b34b-d76291b2089a

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
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_Qx8_herm_smul_left__bcf36eb50b87
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_Qx8_herm_smul_right__34189a3fdce0
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_Qx8_herm_add_left__13aa38a1a87a
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_Qx8_herm_add_right__6879cf36a61e
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx8_herm_conj
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx8_inWb_smul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx8_inWb_add

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
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.P.Qx8
theorem _root_.solution {a b : Fin (2 * r + k + 1) → ℂ} (ha : inWb k r a) (hb : inWb k r b) {A B : ℝ} (hB : 0 < B)
    (haa : herm (Hpk k r) a a = -(A : ℂ)) (hbb : herm (Hpk k r) b b = -(B : ℂ))
    (hG : 0 < Complex.normSq (herm (Hpk k r) a b) - A * B) :
    ∃ (e : Fin (2 * r + k + 1) → ℂ) (s c : ℂ), s ≠ 0 ∧ e = s • (a + c • b) ∧ inWb k r e ∧
      herm (Hpk k r) e b = 0 ∧ herm (Hpk k r) e e = 1 := by
  set ζ := herm (Hpk k r) a b with hζ
  have hBC : (B : ℂ) ≠ 0 := by exact_mod_cast hB.ne'
  set c : ℂ := ζ / B with hc
  set G : ℝ := (Complex.normSq ζ - A * B) / B with hGd
  have hGpos : 0 < G := div_pos hG hB
  set t : ℝ := Real.sqrt G with ht
  have htpos : 0 < t := Real.sqrt_pos.2 hGpos
  have htt : (t : ℂ) * (t : ℂ) = (G : ℂ) := by
    rw [← Complex.ofReal_mul, ht, Real.mul_self_sqrt hGpos.le]
  have htC : (t : ℂ) ≠ 0 := by exact_mod_cast htpos.ne'
  have hba : herm (Hpk k r) b a = star ζ := (herm_conj a b).symm
  have h1 : herm (Hpk k r) (a + c • b) b = 0 := by
    rw [herm_add_left', herm_smul_left', hbb, ← hζ, hc]
    field_simp
    ring
  have hnorm : ζ * star ζ = (Complex.normSq ζ : ℂ) := Complex.mul_conj ζ
  have h2 : herm (Hpk k r) (a + c • b) (a + c • b) = (G : ℂ) := by
    rw [herm_add_right', herm_smul_right', h1, mul_zero, add_zero, herm_add_left', herm_smul_left', haa, hba, hc, hGd]
    push_cast
    rw [← hnorm]
    field_simp
    ring
  refine ⟨(t : ℂ)⁻¹ • (a + c • b), (t : ℂ)⁻¹, c, inv_ne_zero htC, rfl, inWb_smul (inWb_add ha (inWb_smul hb _)) _, ?_,
    ?_⟩
  · rw [herm_smul_left', h1, mul_zero]
  · rw [herm_smul_left', herm_smul_right', h2, ← htt]
    have : star ((t : ℂ)⁻¹) = (t : ℂ)⁻¹ := by
      rw [star_inv₀]
      congr 1
      exact Complex.conj_ofReal t
    rw [this]
    field_simp
end Formalism.FourierDecayAlt.P.Qx8
