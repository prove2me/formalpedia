-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Qx5.pairSum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T02:36:39.655848+00:00
-- url     : https://prove2.me/submissions/52e87958-a133-4093-af4e-fadeeab95719

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumDualVectorEqZeta
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ChainRecursionFromSingleDescent
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_QuantumDetHighestWeightHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ShiftedGeneratorEqIteSmulAdd
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexifiedDerivativeCommutator
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ActualAdjointnessFromHermitian
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx5_oneSide
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyAt_congr
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_congr


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
variable {X : Type*} [AddCommGroup X] [Module ℂ X]
namespace Formalism.FourierDecayAlt.P.Qx5
theorem _root_.solution (n : ℕ) (A ρ B κ : Fin n → ℂ) (G : (Fin (n - 2) → Fin n) → (Fin (n - 2) → Fin n) → X) :
    ∑ i : Fin n, ∑ j : Fin n, ((-1 : ℂ) ^ ((i : ℕ) + (j : ℕ)) * A i * B j) •
        ∑ p : Fin (n - 1), ∑ q : Fin (n - 1), ((-1 : ℂ) ^ ((p : ℕ) + (q : ℕ)) * ρ (skip1 i p) * κ (skip1 j q)) •
          G (skip1 i ∘ skip1 p) (skip1 j ∘ skip1 q) =
      ∑ i : Fin n, ∑ i' : Fin n, ∑ j : Fin n, ∑ j' : Fin n,
        if i < i' ∧ j < j' then
          ((-1 : ℂ) ^ ((i : ℕ) + (i' : ℕ) + (j : ℕ) + (j' : ℕ)) * (A i * ρ i' - A i' * ρ i) * (B j * κ j' - B j' * κ j)) •
            G (skip2 i i') (skip2 j j')
        else 0 := by
  have h1 : ∀ l : Fin (n - 2) → Fin n, _ := fun l => oneSide n B κ (fun l' => G l l')
  have h2 := oneSide n A ρ (fun l => ∑ j : Fin n, ∑ q : Fin (n - 1),
    ((-1 : ℂ) ^ ((j : ℕ) + (q : ℕ)) * B j * κ (skip1 j q)) • G l (skip1 j ∘ skip1 q))
  have L : ∑ i : Fin n, ∑ j : Fin n, ((-1 : ℂ) ^ ((i : ℕ) + (j : ℕ)) * A i * B j) •
        ∑ p : Fin (n - 1), ∑ q : Fin (n - 1), ((-1 : ℂ) ^ ((p : ℕ) + (q : ℕ)) * ρ (skip1 i p) * κ (skip1 j q)) •
          G (skip1 i ∘ skip1 p) (skip1 j ∘ skip1 q) =
      ∑ i : Fin n, ∑ p : Fin (n - 1), ((-1 : ℂ) ^ ((i : ℕ) + (p : ℕ)) * A i * ρ (skip1 i p)) •
        ∑ j : Fin n, ∑ q : Fin (n - 1), ((-1 : ℂ) ^ ((j : ℕ) + (q : ℕ)) * B j * κ (skip1 j q)) •
          G (skip1 i ∘ skip1 p) (skip1 j ∘ skip1 q) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun q _ => ?_
    congr 1
    ring
  rw [L, h2]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun i' _ => ?_
  by_cases hi : i < i'
  · simp only [hi, if_true, true_and, h1, Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun j' _ => ?_
    split_ifs
    · rw [smul_smul]
      congr 1
      ring
    · rw [smul_zero]
  · simp [hi]
end Formalism.FourierDecayAlt.P.Qx5
