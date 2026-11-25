-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Qx8.isStart_pair
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:47:18.643526+00:00
-- url     : https://prove2.me/submissions/79a6b6f8-e5cb-406f-a9b6-af4fe445894f

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
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx8_mkPair_mul_mkPair
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx8_mkPair_sub_mkPair
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx8_star_mkPair
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx8_algebraMap_Pr
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx8_smul_mkP
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_Qx8_mkPair_congr__fe9b39966127
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx8_TJM_apply
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx8_MJT_apply
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx8_smulJ_apply
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx8_epsJ_star
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx8_epsJ_swap
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_PC_Pf_mul_apply
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_PC_kronecker_E1_E2_apply
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_PC_kronecker_embed_mul_apply
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_PC_mul_Pf_apply


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
variable {V : Type} [AddCommGroup V] [Module ℂ V]
namespace Formalism.FourierDecayAlt.P.Qx8
theorem _root_.solution (t : ℂ → Fin 2 → Fin 2 → Module.End ℂ V) (q : ℂ → ℂ) (hq : ∀ Y, star (q Y) = q (star Y))
    (hrtt : ∀ u v a b c d, (u - v) • (t u a b * t v c d - t v c d * t u a b) =
      t u c b * t v a d - t v c b * t u a d)
    (hdet1 : ∀ Y c d, t (Y + 1) 0 c * t Y 1 d - t (Y + 1) 1 c * t Y 0 d = (q Y * epsJ c d) • 1)
    (hdet2 : ∀ Y c d, t Y c 0 * t (Y + 1) d 1 - t Y c 1 * t (Y + 1) d 0 = (q Y * epsJ c d) • 1) :
    Wd.IsStart (pairM t) q ∧ ∀ Y Y', Commute (pairM t Y 1 0) (pairM t Y' 1 0) := by
  have hent : ∀ (u v : ℂ) (i j k l : Fin 2),
      (u - v) • (pairM t u i j * pairM t v k l - pairM t v k l * pairM t u i j) =
        pairM t u k j * pairM t v i l - pairM t v k j * pairM t u i l := by
    intro u v i j k l
    simp only [pairM, Matrix.of_apply, mkPair_mul_mkPair, mkPair_sub_mkPair, smul_mkP]
    refine mkPair_congr' (hrtt u v i j k l) ?_
    have h := hrtt (star u) (star v) j i l k
    rw [star_sub, ← neg_inj, ← smul_neg, neg_sub, neg_sub]
    exact h
  have hcomm : ∀ (a b : Fin 2) (u v : ℂ), t u a b * t v a b = t v a b * t u a b := by
    intro a b u v
    have h1 := hrtt u v a b a b
    have h2 := hrtt v u a b a b
    have e1 : (u - v - 1) • (t u a b * t v a b - t v a b * t u a b) = 0 := by
      rw [sub_smul, one_smul, h1, sub_self]
    have e2 : (u - v + 1) • (t u a b * t v a b - t v a b * t u a b) = 0 := by
      have : (v - u - 1) • (t v a b * t u a b - t u a b * t v a b) = 0 := by
        rw [sub_smul, one_smul, h2, sub_self]
      rw [← neg_sub (t u a b * t v a b), smul_neg, ← neg_smul] at this
      rw [← this]
      congr 1
      ring
    have e3 : (2 : ℂ) • (t u a b * t v a b - t v a b * t u a b) = 0 := by
      have : (2 : ℂ) = (u - v + 1) - (u - v - 1) := by ring
      rw [this, sub_smul, e1, e2, sub_zero]
    exact sub_eq_zero.mp ((smul_eq_zero.mp e3).resolve_left two_ne_zero)
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · intro Y hY
    ext a b : 1
    rw [Matrix.conjTranspose_apply]
    simp only [pairM, Matrix.of_apply, star_mkPair, hY]
  · intro Y Y'
    apply Matrix.ext
    rintro ⟨i, k⟩ ⟨j, l⟩
    rw [Matrix.mul_assoc, Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.one_mul, Matrix.mul_one, Matrix.sub_apply, Matrix.sub_apply, Matrix.smul_apply,
      Matrix.smul_apply, Mx6.PC.Pf_mul_apply, Mx6.PC.mul_Pf_apply, Mx6.PC.kronecker_E1_E2_apply, Mx6.PC.kronecker_E1_E2_apply,
      Mx6.PC.kronecker_embed_mul_apply, Mx6.PC.kronecker_embed_mul_apply]
    have h := hent Y' Y i j k l
    rw [smul_sub] at h
    rw [sub_eq_sub_iff_sub_eq_sub]
    exact h
  · intro Y
    constructor
    · ext c d : 1
      rw [TJM_apply, smulJ_apply, algebraMap_Pr]
      simp only [pairM, Matrix.of_apply, mkPair_mul_mkPair, mkPair_sub_mkPair]
      refine mkPair_congr' ?_ ?_
      · rw [hdet1, Algebra.algebraMap_eq_smul_one]
      · have h := hdet2 (star Y) d c
        rw [star_add, star_one, ← neg_sub, h, Algebra.algebraMap_eq_smul_one, star_mul', hq, epsJ_star,
          epsJ_swap c d, ← neg_smul]
        congr 1
        ring
    · ext c d : 1
      rw [MJT_apply, smulJ_apply, algebraMap_Pr]
      simp only [pairM, Matrix.of_apply, mkPair_mul_mkPair, mkPair_sub_mkPair]
      refine mkPair_congr' ?_ ?_
      · rw [hdet2, Algebra.algebraMap_eq_smul_one]
      · have h := hdet1 (star Y) d c
        rw [star_add, star_one, ← neg_sub, h, Algebra.algebraMap_eq_smul_one, star_mul', hq, epsJ_star,
          epsJ_swap c d, ← neg_smul]
        congr 1
        ring
  · intro Y hY
    rw [hq, hY]
  · intro Y Y'
    show pairM t Y 1 0 * pairM t Y' 1 0 = pairM t Y' 1 0 * pairM t Y 1 0
    simp only [pairM, Matrix.of_apply, mkPair_mul_mkPair]
    exact mkPair_congr' (hcomm 1 0 Y Y') (hcomm 0 1 _ _)
end Formalism.FourierDecayAlt.P.Qx8
