-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Wd7.QQ_transpose
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:52:13.03726+00:00
-- url     : https://prove2.me/submissions/d1c23b9e-f9e5-4f1d-868b-35e0f910795c

import Definitions.Def_Formalism_HermitianCurvature_StatementWd
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EntryCommuteTransposedRMatrix
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ScalarCommuteTransposedRMatrixEntry
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd7_transpose_mul_of_comm
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd7_commute_Avr_Bvr_of_commute_siteOps
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd7_comm_Tstar
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd7_mem_ops_hol
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd7_mem_ops_star
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd7_comm_T_Tstar
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd6_commute_Avr_Bvr_of_commute_siteOps
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd6_transpose_mul_of_comm


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Wd7
open Matrix Formalism.YangianSpanCharacter.T Formalism.FourierDecayAlt.W Formalism.FourierDecayAlt.Wd
variable {K A S : Type} [Field K] [StarRing K] [Ring A] [StarRing A] [Algebra K A] [StarModule K A]
  [Fintype S] [DecidableEq S]
namespace Formalism.FourierDecayAlt.P.Wd7
theorem _root_.solution (σ : Site A) (hσ : IsSite σ) (Q : M2 A) (Y : K)
    (hQ : ∀ i j, ∀ x ∈ ops σ, Commute (Q i j) x) :
    ((Ts σ Y)ᴴ * Q * Ts σ Y)ᵀ = (Ts σ Y)ᵀ * Qᵀ * (Ts σ Y).map star := by
  have hQT : ∀ i j k l, Commute (Q i j) (Ts σ Y k l) := fun i j k l =>
    commute_Avr_Bvr_of_commute_siteOps σ Y _ (fun x hx => hQ i j x (mem_ops_hol hx)) k l
  have hQS : ∀ i j k l, Commute (Q i j) (star (Ts σ Y k l)) := fun i j k l =>
    comm_Tstar σ Y _ (fun x hx => hQ i j _ (mem_ops_star hx)) k l
  rw [transpose_mul_of_comm, transpose_mul_of_comm]
  · rw [mul_assoc]
    rfl
  · intro i j k l
    exact (hQS k l j i).symm
  · intro i j k l
    rw [Matrix.mul_apply]
    refine Commute.sum_left _ _ _ fun m _ => Commute.mul_left ?_ (hQT m j k l)
    exact (comm_T_Tstar σ hσ Y Y k l m i).symm
end Formalism.FourierDecayAlt.P.Wd7
