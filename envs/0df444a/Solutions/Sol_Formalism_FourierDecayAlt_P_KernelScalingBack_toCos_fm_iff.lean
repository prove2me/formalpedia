-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.KernelScalingBack.toCos_fm_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:25:11.593103+00:00
-- url     : https://prove2.me/submissions/cfe810fb-8b00-453d-9327-655a6ad50153

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ColumnOperationTripleForm
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelNonzeroModulusDeterminantEq
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstKernelExplicitFormula
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LatticeAverageIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelScalingBack
import Theorems.Thm_Formalism_FourierDecayAlt_P_KernelScalingBack_cj_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_KernelScalingBack_cj_inv
import Theorems.Thm_Formalism_FourierDecayAlt_P_KernelScalingBack_isInt_cj
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x7_mem_intSub


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Filter Topology
open scoped ComplexConjugate
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.KernelScalingBack
variable {K : Type} [CommRing K] (R : Subring K) (S : List ℕ) (T c : ℕ → Kˣ)
variable (hc : ∀ b, ((c b : Kˣ) : K) ∈ R ∧ (((c b)⁻¹ : Kˣ) : K) ∈ R)
include hc
namespace Formalism.FourierDecayAlt.P.KernelScalingBack
theorem _root_.solution (p p₁ : lowW K S T × upUniG K S.sum) :
    A5x8.toCos R (w := ((S, T * c) : Point K)) (fm S T c p) =
        A5x8.toCos R (w := ((S, T * c) : Point K)) (fm S T c p₁) ↔
      A5x8.toCos R (w := ((S, T) : Point K)) p = A5x8.toCos R (w := ((S, T) : Point K)) p₁ := by
  unfold A5x8.toCos
  rw [Prod.mk.injEq, Prod.mk.injEq]
  refine and_congr ?_ ?_
  · rw [Quotient.eq, Quotient.eq, QuotientGroup.rightRel_apply, QuotientGroup.rightRel_apply]
    exact Iff.rfl
  · rw [QuotientGroup.eq, QuotientGroup.eq, A5x7.mem_intSub, A5x7.mem_intSub]
    have e : (((fm S T c p).2⁻¹ * (fm S T c p₁).2 : upUniG K S.sum) : GL (Fin S.sum) K) =
        cj (dg S c) ((p.2⁻¹ * p₁.2 : upUniG K S.sum) : GL (Fin S.sum) K) := by
      show (cj (dg S c) p.2.1)⁻¹ * cj (dg S c) p₁.2.1 = cj (dg S c) (p.2.1⁻¹ * p₁.2.1)
      rw [cj_mul, cj_inv]
    have hd : ∀ b, ((dg S c b : Kˣ) : K) ∈ R ∧ (((dg S c b)⁻¹ : Kˣ) : K) ∈ R := fun b => hc _
    show IsInt R ((((fm S T c p).2⁻¹ * (fm S T c p₁).2 : upUniG K S.sum) : GL (Fin S.sum) K) :
        Matrix (Fin S.sum) (Fin S.sum) K) ∧
      IsInt R (((((fm S T c p).2⁻¹ * (fm S T c p₁).2 : upUniG K S.sum) : GL (Fin S.sum) K)⁻¹ :
        GL (Fin S.sum) K) : Matrix (Fin S.sum) (Fin S.sum) K) ↔ _
    rw [e, ← cj_inv, isInt_cj R _ hd, isInt_cj R _ hd]
end Formalism.FourierDecayAlt.P.KernelScalingBack
