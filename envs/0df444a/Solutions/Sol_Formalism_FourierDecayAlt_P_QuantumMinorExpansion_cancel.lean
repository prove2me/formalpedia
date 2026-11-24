-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.QuantumMinorExpansion.cancel
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T17:55:13.195412+00:00
-- url     : https://prove2.me/submissions/37172dc1-5d2a-49ba-8b02-edd3b1e0ffa6

import Definitions.Def_Formalism_HermitianCurvature_StatementQr
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LemmaDDeterminantIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ChainRecursionFromSingleDescent
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_QuantumDetHighestWeightHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ShiftedGeneratorEqIteSmulAdd
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_GeneratorCommutatorQuantumDet
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QuantumMinorExpansion
import Theorems.Thm_Formalism_FourierDecayAlt_P_QuantumMinorExpansion_Tm_EX
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyAt_succ
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_at
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_succ


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Polynomial
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.QuantumMinorExpansion
open Formalism.REAL Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr Formalism.FourierDecayAlt.P.Qx6
variable {A : Type} [Ring A] [Algebra ℂ A] {n : ℕ} (E : Fin n → Fin n → A)
namespace Formalism.FourierDecayAlt.P.QuantumMinorExpansion
theorem _root_.solution (Z : Fin n → A[X]) (v : ℂ) (h : ∀ c, ∑ p, Z p * Tm (EX E) v c p = 0) : ∀ p, Z p = 0 := by
  have step : ∀ k, (∀ p, (Z p).coeff (k + 1) = 0) → ∀ p, (Z p).coeff k = 0 := by
    intro k hk c
    have h1 := congrArg (fun f => coeff f (k + 1)) (h c)
    simp only [Tm_EX, mul_add, Finset.sum_add_distrib, coeff_add, finsetSum_coeff, coeff_mul_C, hk, zero_mul,
      Finset.sum_const_zero, zero_add, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true, coeff_mul_X,
      coeff_zero] at h1
    exact h1
  have all : ∀ N, (∀ k, N ≤ k → ∀ p, (Z p).coeff k = 0) → ∀ k p, (Z p).coeff k = 0 := by
    intro N
    induction N with
    | zero => intro h k p; exact h k (Nat.zero_le _) p
    | succ N ih =>
      intro h
      apply ih
      intro k hk
      rcases Nat.eq_or_lt_of_le hk with rfl | hlt
      · exact step _ (h _ le_rfl)
      · exact h k hlt
  intro p
  ext k
  rw [coeff_zero]
  refine all (Finset.univ.sup (fun p => (Z p).natDegree) + 1) ?_ k p
  intro k hk p
  apply coeff_eq_zero_of_natDegree_lt
  have := Finset.le_sup (f := fun p => (Z p).natDegree) (Finset.mem_univ p)
  omega
end Formalism.FourierDecayAlt.P.QuantumMinorExpansion
