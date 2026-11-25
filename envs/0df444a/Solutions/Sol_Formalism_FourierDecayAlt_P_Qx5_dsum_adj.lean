-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Qx5.dsum_adj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:16:10.209844+00:00
-- url     : https://prove2.me/submissions/66d80cae-e8b6-4d0b-a302-d90b95dd7415

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumDualVectorEqZeta
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ChainRecursionFromSingleDescent
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_QuantumDetHighestWeightHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ShiftedGeneratorEqIteSmulAdd
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexifiedDerivativeCommutator
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ActualAdjointnessFromHermitian
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx5_dP_four
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyAt_succ
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_at
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_succ
import Theorems.Thm_Formalism_REAL_eq_zero_of_add_self_eq_zero


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
theorem _root_.solution (E : Fin n → Fin n → A) {m : ℕ} (a b : Fin (m + 1) → Fin n) (θ : Fin (m + 1) → ℂ) (i : Fin m) :
    dsum E a b (θ ∘ Equiv.swap i.castSucc i.succ) = dsum E a b θ := by
  set s := Equiv.swap i.castSucc i.succ with hs_def
  have hsgn : Equiv.Perm.sign s = -1 := Equiv.Perm.sign_swap (by simp [Fin.ext_iff])
  set G : Equiv.Perm (Fin (m + 1)) → Equiv.Perm (Fin (m + 1)) → A := fun τ σ =>
    ((Equiv.Perm.sign τ : ℤ) : A) * (((Equiv.Perm.sign σ : ℤ) : A) * (dP E a b θ σ τ - dP E a b (θ ∘ s) σ τ)) with hG
  have hsum : dsum E a b θ - dsum E a b (θ ∘ s) = ∑ τ, ∑ σ, G τ σ := by
    unfold dsum
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun σ _ => ?_
    simp only [hG, mul_sub]
  have hre : ∑ τ, ∑ σ, G (τ * s) (σ * s) = ∑ τ, ∑ σ, G τ σ := by
    rw [Fintype.sum_equiv (Equiv.mulRight s) (fun τ => ∑ σ, G (τ * s) (σ * s)) (fun τ => ∑ σ, G τ (σ * s))
      (fun τ => rfl)]
    refine Finset.sum_congr rfl fun τ _ => ?_
    exact Fintype.sum_equiv (Equiv.mulRight s) _ _ (fun σ => rfl)
  have hpair : ∀ τ σ, G τ σ + G (τ * s) (σ * s) = 0 := by
    intro τ σ
    simp only [hG, Equiv.Perm.sign_mul, hsgn, mul_neg, mul_one, Units.val_neg, Int.cast_neg, neg_mul, neg_neg]
    have k := dP_four E a b θ i σ τ
    rw [← hs_def] at k
    calc _ = ((Equiv.Perm.sign τ : ℤ) : A) * (((Equiv.Perm.sign σ : ℤ) : A) * (dP E a b θ σ τ - dP E a b (θ ∘ s) σ τ
        + dP E a b θ (σ * s) (τ * s) - dP E a b (θ ∘ s) (σ * s) (τ * s))) := by noncomm_ring
      _ = 0 := by rw [k, mul_zero, mul_zero]
  have h0 : (∑ τ, ∑ σ, G τ σ) + (∑ τ, ∑ σ, G τ σ) = 0 := by
    calc (∑ τ, ∑ σ, G τ σ) + (∑ τ, ∑ σ, G τ σ) = (∑ τ, ∑ σ, G τ σ) + ∑ τ, ∑ σ, G (τ * s) (σ * s) := by rw [hre]
      _ = ∑ τ, ∑ σ, (G τ σ + G (τ * s) (σ * s)) := by simp only [Finset.sum_add_distrib]
      _ = 0 := by simp only [hpair, Finset.sum_const_zero]
  have := eq_zero_of_add_self_eq_zero _ h0
  rw [← hsum] at this
  exact (sub_eq_zero.1 this).symm
end Formalism.FourierDecayAlt.P.Qx5
