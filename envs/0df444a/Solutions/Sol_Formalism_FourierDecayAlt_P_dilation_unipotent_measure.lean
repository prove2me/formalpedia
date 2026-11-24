-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.dilation_unipotent_measure
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T15:36:37.817969+00:00
-- url     : https://prove2.me/submissions/5f4f8789-65b5-4119-906f-1faafd24d2e5

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_dg_mid
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_dg_mul_inv
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_aDil_mem
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_conj_apply
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_dg_step
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_dg_last
import Theorems.Thm_Formalism_QuantumDeterminants_WeylGroupFacts_nset_iff
import Theorems.Thm_Formalism_QuantumDeterminants_WeylGroupFacts_uh_inv
import Theorems.Thm_Formalism_QuantumDeterminants_WeylGroupFacts_uh_mul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.B4
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.B.DilN := by
  intro k r z t ht hz n hn
  have hn' := (WeylGroupFacts.nset_iff n).1 hn
  have hell : ell k r z (aDil k r t * n * (aDil k r t)⁻¹) = (t : ℂ) * ell k r z n := by
    unfold ell
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    by_cases h : a.val + 1 < r
    · simp only [h, dif_pos]
      rw [conj_apply k r t ht, mul_right_comm, dg_step k r t ht a h]
    · simp only [h, dif_neg, not_false_eq_true]
      simp only [Matrix.mulVec, dotProduct]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [conj_apply k r t ht, dg_last k r t a h]
      by_cases hj : j.val < r ∨ r + k < j.val
      · rw [hz j hj]; simp
      · rw [dg_mid k r t⁻¹ j (by omega) (by omega)]; ring
  refine ⟨?_, hell, ?_⟩
  · rw [WeylGroupFacts.nset_iff]
    refine ⟨WeylGroupFacts.uh_mul (WeylGroupFacts.uh_mul (aDil_mem k r t ht) hn'.1) (WeylGroupFacts.uh_inv (aDil_mem k r t ht)), ?_⟩
    intro i j hj hi
    rw [conj_apply k r t ht, hn'.2 i j hj hi]
    by_cases hij : i = j
    · subst hij
      simp [dg_mul_inv k r t ht i]
    · simp [hij]
  · unfold lam
    rw [hell, mul_left_comm, Complex.re_ofReal_mul]
end Formalism.FourierDecayAlt.P
