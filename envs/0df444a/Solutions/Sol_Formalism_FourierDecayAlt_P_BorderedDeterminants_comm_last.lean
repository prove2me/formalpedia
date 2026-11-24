-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.BorderedDeterminants.comm_last
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T18:05:51.061697+00:00
-- url     : https://prove2.me/submissions/31bb47ff-e884-4ce5-a266-69bf3afdd231

import Definitions.Def_Formalism_HermitianCurvature_CapelliDeterminantAndBranching
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LemmaDDeterminantIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ChainRecursionFromSingleDescent
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QuantumMinorCommutation
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_QuantumDetHighestWeightHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ShiftedGeneratorEqIteSmulAdd
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_GeneratorCommutatorQuantumDet
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BorderedDeterminants
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_at


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.BorderedDeterminants
open Formalism.REAL Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr
variable {V : Type} [AddCommGroup V] [Module ℂ V]
namespace Formalism.FourierDecayAlt.P.BorderedDeterminants
theorem _root_.solution {n : ℕ} (E : Fin (n + 1) → Fin (n + 1) → Module.End ℂ V) (hE : GlRel E) (c u : ℂ) :
    Commute (Tm E c (Fin.last n) (Fin.last n)) (qdet (subA E) u) := by
  have hc : ∀ a b : Fin n, Commute (E (Fin.last n) (Fin.last n)) (subA E a b) := by
    intro a b
    have h := hE (Fin.last n) (Fin.last n) a.castSucc b.castSucc
    rw [if_neg (Fin.castSucc_lt_last a).ne', if_neg (Fin.castSucc_lt_last b).ne, sub_zero] at h
    exact sub_eq_zero.mp h
  have hT : ∀ w (a b : Fin n), Commute (Tm E c (Fin.last n) (Fin.last n)) (Tm (subA E) w a b) := by
    intro w a b
    unfold Tm
    rw [if_pos (rfl : Fin.last n = Fin.last n)]
    apply Commute.add_left
    · exact Algebra.commute_algebraMap_left _ _
    · apply Commute.add_right
      · split_ifs
        · exact Algebra.commute_algebraMap_right _ _
        · exact Commute.zero_right _
      · exact hc a b
  unfold qdet qminor
  refine Commute.sum_right _ _ _ (fun σ _ => ?_)
  refine Commute.mul_right (Int.cast_commute _ _).symm ?_
  refine Commute.list_prod_right _ _ (fun y hy => ?_)
  simp only [List.mem_ofFn, Set.mem_range] at hy
  obtain ⟨k, rfl⟩ := hy
  exact hT _ _ _
end Formalism.FourierDecayAlt.P.BorderedDeterminants
