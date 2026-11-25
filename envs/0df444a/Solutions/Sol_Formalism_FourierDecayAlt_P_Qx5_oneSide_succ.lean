-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Qx5.oneSide_succ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T01:50:28.23028+00:00
-- url     : https://prove2.me/submissions/f7758df3-ac36-404f-9324-b6751286a0e2

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumDualVectorEqZeta
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ChainRecursionFromSingleDescent
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_QuantumDetHighestWeightHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ShiftedGeneratorEqIteSmulAdd
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexifiedDerivativeCommutator
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ActualAdjointnessFromHermitian
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyAt_congr
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_congr
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx6_sign_pair_succAbove_right
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx6_skip_two_succAbove_comp_alt
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx6_sum_ne_succAbove


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
theorem _root_.solution (M : ℕ) (α β : Fin (M + 2) → ℂ) (H : (Fin M → Fin (M + 2)) → X) :
    ∑ i : Fin (M + 2), ∑ p : Fin (M + 1), ((-1 : ℂ) ^ ((i : ℕ) + (p : ℕ)) * α i * β (i.succAbove p)) •
        H (i.succAbove ∘ p.succAbove) =
      ∑ i : Fin (M + 2), ∑ i' : Fin (M + 2),
        if i < i' then ((-1 : ℂ) ^ ((i : ℕ) + (i' : ℕ)) * (α i' * β i - α i * β i')) • H (skip2 i i') else 0 := by
  set T : Fin (M + 2) → Fin (M + 2) → X := fun i W =>
    (((sg2 i W : ℤ) : ℂ) * α i * β W) • H (skip2 (min W i) (max W i)) with hT
  have s1 : ∀ i : Fin (M + 2), ∑ p : Fin (M + 1), ((-1 : ℂ) ^ ((i : ℕ) + (p : ℕ)) * α i * β (i.succAbove p)) •
      H (i.succAbove ∘ p.succAbove) = ∑ W : Fin (M + 2), if W ≠ i then T i W else 0 := by
    intro i
    rw [Qx6.sum_ne_succAbove i (fun W => T i W)]
    refine Finset.sum_congr rfl fun p _ => ?_
    simp only [hT, Qx6.sign_pair_succAbove_right, Qx6.skip_two_succAbove_comp_alt]
    push_cast
    rfl
  have s2 : ∀ i W : Fin (M + 2), (if W ≠ i then T i W else 0) =
      (if i < W then T i W else 0) + (if W < i then T i W else 0) := by
    intro i W
    rcases lt_trichotomy i W with h | h | h
    · simp [h, h.ne', not_lt.2 h.le]
    · simp [h]
    · simp [h, h.ne, not_lt.2 h.le]
  simp only [s1, s2, Finset.sum_add_distrib]
  rw [Finset.sum_comm (f := fun i W => if W < i then T i W else 0), ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i' _ => ?_
  by_cases h : i < i'
  · have h' : (i : ℕ) < (i' : ℕ) := h
    simp only [h, if_true, hT, sg2, min_eq_right h.le, max_eq_left h.le, min_eq_left h.le, max_eq_right h.le,
      if_neg (not_lt.2 h'.le), if_pos h', ← add_smul]
    congr 1
    push_cast
    ring
  · simp [h]
end Formalism.FourierDecayAlt.P.Qx5
