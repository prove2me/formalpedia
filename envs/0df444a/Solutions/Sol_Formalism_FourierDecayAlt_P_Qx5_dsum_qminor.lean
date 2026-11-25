-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Qx5.dsum_qminor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T02:24:58.877334+00:00
-- url     : https://prove2.me/submissions/f1799b53-9c9a-4599-b0c6-3371dba44b64

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumDualVectorEqZeta
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ChainRecursionFromSingleDescent
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_QuantumDetHighestWeightHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ShiftedGeneratorEqIteSmulAdd
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexifiedDerivativeCommutator
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ActualAdjointnessFromHermitian
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx5_sign_sq
import Theorems.Thm_Formalism_REAL_quantumMinorColSkew_holds


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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Qx5
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {A : Type} [Ring A] [Algebra ℂ A] {n : ℕ}
namespace Formalism.FourierDecayAlt.P.Qx5
theorem _root_.solution {E : Fin n → Fin n → A} (hE : GlRel E) {t : ℕ} (a b : Fin t → Fin n) (w : ℂ) :
    dsum E a b (fun k => w - ((k : ℕ) : ℂ)) = (Fintype.card (Equiv.Perm (Fin t)) : ℂ) • qminor E a b w := by
  have h : ∀ τ : Equiv.Perm (Fin t), ∑ σ : Equiv.Perm (Fin t),
      ((Equiv.Perm.sign τ : ℤ) : A) * (((Equiv.Perm.sign σ : ℤ) : A) * dP E a b (fun k => w - ((k : ℕ) : ℂ)) σ τ) =
      qminor E a b w := by
    intro τ
    rw [← Finset.mul_sum]
    have : ∑ σ : Equiv.Perm (Fin t), ((Equiv.Perm.sign σ : ℤ) : A) * dP E a b (fun k => w - ((k : ℕ) : ℂ)) σ τ =
        qminor E a (b ∘ τ) w := rfl
    rw [this, quantumMinorColSkew_holds A n t E hE a b τ w, sign_sq]
  unfold dsum
  simp only [h, Finset.sum_const, Finset.card_univ]
  rw [Nat.cast_smul_eq_nsmul]
end Formalism.FourierDecayAlt.P.Qx5
