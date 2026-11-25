-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Qx8.Nlev_last
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T01:47:36.820207+00:00
-- url     : https://prove2.me/submissions/3a80bb37-2f3f-45f0-bdd0-5dee7f0d508e

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
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx8_herm_UH
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx8_herm_bvec_right
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx8_Hpk_mulVec
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx8_mulVec_bvec
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x3_mulVec_bvec
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_herm_UH
import Theorems.Thm_Formalism_QuantumDeterminants_BruhatBigCell_mulVec_bvec
import Theorems.Thm_Formalism_QuantumDeterminants_GBasic_sig_hi


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
namespace Formalism.FourierDecayAlt.P.Qx8
theorem _root_.solution {k r : ℕ} {n : Mx k r} (hn : n ∈ Nlev k r (Fin.last r)) : n = 1 := by
  obtain ⟨⟨hU, -, h3⟩, -, hfix⟩ := hn
  ext i j
  by_cases hj1 : j.val < r
  · have h := (hfix ⟨j.val, hj1⟩ (by simpa using hj1)).1
    have e : eI k r ⟨j.val, hj1⟩ = j := Fin.ext rfl
    rw [e] at h
    have := congrFun h i
    rw [mulVec_bvec] at this
    rw [this, Matrix.one_apply, bvec, Pi.single_apply]
  by_cases hj2 : r + k < j.val
  · have hjl := j.isLt
    have ha : 2 * r + k - j.val < r := by omega
    have h := (hfix ⟨2 * r + k - j.val, ha⟩ (by simpa using ha)).2
    have e : esI k r ⟨2 * r + k - j.val, ha⟩ = j := Fin.ext (by simp only [esI]; omega)
    rw [e] at h
    have := congrFun h i
    rw [mulVec_bvec] at this
    rw [this, Matrix.one_apply, bvec, Pi.single_apply]
  by_cases hi : r ≤ i.val
  · rw [h3 i j (by omega) (by omega) hi, Matrix.one_apply]
  · have hi' : i.val < r := by omega
    have h := (hfix ⟨i.val, hi'⟩ (by simpa using hi')).2
    have h1 := herm_UH hU (bvec j) (bvec (esI k r ⟨i.val, hi'⟩))
    rw [h, herm_bvec_right, herm_bvec_right, Hpk_mulVec, Hpk_mulVec] at h1
    have es : GBasic.sig k r (esI k r ⟨i.val, hi'⟩) = i := by
      apply Fin.ext
      have hv : (esI k r ⟨i.val, hi'⟩).val = 2 * r + k - i.val := rfl
      rw [GBasic.sig_hi k r _ (by rw [hv]; omega), hv]
      omega
    have sg : GBasic.sgn k r (esI k r ⟨i.val, hi'⟩) = 1 := by
      have hv : (esI k r ⟨i.val, hi'⟩).val = 2 * r + k - i.val := rfl
      unfold GBasic.sgn
      rw [if_neg (by rw [hv]; omega)]
    rw [es, sg, one_mul, one_mul, mulVec_bvec] at h1
    rw [h1, Matrix.one_apply, bvec, Pi.single_apply]
end Formalism.FourierDecayAlt.P.Qx8
