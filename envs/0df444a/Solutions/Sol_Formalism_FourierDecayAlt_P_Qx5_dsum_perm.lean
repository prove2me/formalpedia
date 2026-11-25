-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Qx5.dsum_perm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T05:50:49.560346+00:00
-- url     : https://prove2.me/submissions/d8b07f0f-7e13-473b-bb43-e05feec1e695

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumDualVectorEqZeta
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ChainRecursionFromSingleDescent
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_QuantumDetHighestWeightHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ShiftedGeneratorEqIteSmulAdd
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexifiedDerivativeCommutator
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ActualAdjointnessFromHermitian
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx5_dsum_adj
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyAt_succ
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_succ


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
theorem _root_.solution (E : Fin n → Fin n → A) {t : ℕ} (a b : Fin t → Fin n) (θ : Fin t → ℂ) (π : Equiv.Perm (Fin t)) :
    dsum E a b (θ ∘ π) = dsum E a b θ := by
  cases t with
  | zero =>
    have : π = 1 := Subsingleton.elim _ _
    subst this; rfl
  | succ m =>
    have hπ : π ∈ Submonoid.closure (Set.range fun i : Fin m => Equiv.swap i.castSucc i.succ) := by
      rw [Equiv.Perm.mclosure_swap_castSucc_succ m]; trivial
    induction hπ using Submonoid.closure_induction generalizing θ with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      exact dsum_adj E a b θ i
    | one => rfl
    | mul x y _ _ hx hy =>
      have hc : θ ∘ ⇑(x * y) = (θ ∘ ⇑x) ∘ ⇑y := by ext k; simp
      rw [hc, hy (θ ∘ ⇑x), hx θ]
end Formalism.FourierDecayAlt.P.Qx5
