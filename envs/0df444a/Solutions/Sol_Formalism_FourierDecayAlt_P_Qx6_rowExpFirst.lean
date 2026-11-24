-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Qx6.rowExpFirst
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T18:22:17.721594+00:00
-- url     : https://prove2.me/submissions/ca5c808b-0936-41b3-a42f-b265e734c8e0

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_GeneratorCommutatorQuantumDet
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumDualVectorEqZeta
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeylCellConjTransposeMulApply
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ChainRecursionFromSingleDescent
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx6_firstColumnSplit_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx6_firstColumnSplit_succ
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx6_sign_insert_perm
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx6_firstColumnSplit_bijective
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_Good_comp
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
open Matrix Finset Filter Topology
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Qx6
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q
namespace Formalism.FourierDecayAlt.P.Qx6
theorem _root_.solution {A : Type*} [Ring A] [Algebra ℂ A] {n t : ℕ} (E : Fin n → Fin n → A)
    (a b : Fin (t + 1) → Fin n) (u : ℂ) :
    qminorRow E a b u = ∑ l : Fin (t + 1), (((-1 : ℤ) ^ (l : ℕ) : ℤ) : A) *
        (Tm E (u - (t : ℂ)) (a 0) (b l) * qminorRow E (a ∘ Fin.succ) (b ∘ l.succAbove) u) := by
  unfold qminorRow
  rw [(Fintype.sum_bijective _ (firstColumnSplit_bijective t) _ _ (fun _ => rfl)).symm, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun τ _ => ?_)
  rw [List.ofFn_succ, List.prod_cons]
  simp only [sign_insert_perm, firstColumnSplit_zero, firstColumnSplit_succ, Function.comp, Fin.val_zero, Fin.val_succ]
  have e1 : u - ((t + 1 : ℕ) : ℂ) + 1 + ((0 : ℕ) : ℂ) = u - (t : ℂ) := by push_cast; ring
  have e2 : ∀ i : Fin t, u - ((t + 1 : ℕ) : ℂ) + 1 + (((i : ℕ) + 1 : ℕ) : ℂ) = u - (t : ℂ) + 1 + ((i : ℕ) : ℂ) := by
    intro i; push_cast; ring
  simp only [e1, e2]
  have hc : ∀ x : A, ((Equiv.Perm.sign τ : ℤ) : A) * x = x * ((Equiv.Perm.sign τ : ℤ) : A) :=
    fun x => (Int.cast_commute _ _).eq
  push_cast
  simp only [mul_assoc]
  rw [← mul_assoc (Tm E (u - (t : ℂ)) (a 0) (b j)), ← hc, mul_assoc]
end Formalism.FourierDecayAlt.P.Qx6
