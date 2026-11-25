-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Qx5.dP_four
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T03:39:07.264872+00:00
-- url     : https://prove2.me/submissions/ea6b9bc8-8e51-4305-afec-7a2e891f432b

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumDualVectorEqZeta
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ChainRecursionFromSingleDescent
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_QuantumDetHighestWeightHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ShiftedGeneratorEqIteSmulAdd
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexifiedDerivativeCommutator
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ActualAdjointnessFromHermitian
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx5_mid_id
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyAt_succ
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_succ
import Theorems.Thm_Formalism_REAL_prod_ofFn_alternating_sum


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
theorem _root_.solution (E : Fin n → Fin n → A) {m : ℕ} (a b : Fin (m + 1) → Fin n) (θ : Fin (m + 1) → ℂ) (i : Fin m)
    (σ τ : Equiv.Perm (Fin (m + 1))) :
    dP E a b θ σ τ - dP E a b (θ ∘ Equiv.swap i.castSucc i.succ) σ τ
      + dP E a b θ (σ * Equiv.swap i.castSucc i.succ) (τ * Equiv.swap i.castSucc i.succ)
      - dP E a b (θ ∘ Equiv.swap i.castSucc i.succ) (σ * Equiv.swap i.castSucc i.succ)
          (τ * Equiv.swap i.castSucc i.succ) = 0 := by
  have hs : ∀ k : Fin (m + 1), (k : ℕ) ≠ (i : ℕ) → (k : ℕ) ≠ (i : ℕ) + 1 →
      Equiv.swap i.castSucc i.succ k = k := by
    intro k h1 h2
    apply Equiv.swap_apply_of_ne_of_ne
    · intro h; apply h1; rw [h]; simp
    · intro h; apply h2; rw [h]; simp
  unfold dP
  apply prod_ofFn_alternating_sum _ _ _ _ (i : ℕ) (by omega)
  · intro k h1 h2; simp [hs k h1 h2]
  · intro k h1 h2; simp [Equiv.Perm.mul_apply, hs k h1 h2]
  · intro k h1 h2; simp [Equiv.Perm.mul_apply, hs k h1 h2]
  · have e1 : (⟨(i : ℕ), by omega⟩ : Fin (m + 1)) = i.castSucc := rfl
    have e2 : (⟨(i : ℕ) + 1, by omega⟩ : Fin (m + 1)) = i.succ := rfl
    simp only [e1, e2, Equiv.Perm.mul_apply, Function.comp_apply, Equiv.swap_apply_left,
      Equiv.swap_apply_right]
    exact mid_id E _ _ _ _ _ _
end Formalism.FourierDecayAlt.P.Qx5
