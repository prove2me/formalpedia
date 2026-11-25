-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.quantum_minor_covariance
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:38:04.551097+00:00
-- url     : https://prove2.me/submissions/30b26b93-d3ce-4aef-a6fd-224c9abb5f1e

import Definitions.Def_Formalism_HermitianCurvature_StatementQr
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LemmaDDeterminantIdentity
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_QuantumDetHighestWeightHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ShiftedGeneratorEqIteSmulAdd
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_GeneratorCommutatorQuantumDet
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QuantumMinorCommutation
import Theorems.Thm_Formalism_FourierDecayAlt_P_QuantumMinorCommutation_commute_qminor
import Theorems.Thm_Formalism_FourierDecayAlt_P_QuantumMinorCommutation_minorCov_succ
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
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.Qr.MinorCov := by
  intro A _ _ t E η hE hη u q p i
  by_cases hip : i = p
  · rw [if_pos hip, sub_eq_zero]
    refine (Formalism.FourierDecayAlt.P.QuantumMinorCommutation.commute_qminor E _ _ u _ (fun s s' => ?_)).eq.symm
    have := hη (Formalism.FourierDecayAlt.Q.skip1 q s) (Formalism.FourierDecayAlt.Q.skip1 p s') i
    have hne : Formalism.FourierDecayAlt.Q.skip1 p s' ≠ i := by
      rw [hip]
      intro h
      have h' := congrArg Fin.val h
      unfold Formalism.FourierDecayAlt.Q.skip1 at h'
      split_ifs at h' <;> simp only [] at h' <;> omega
    rw [if_neg hne, sub_eq_zero] at this
    exact this.symm
  · rw [if_neg hip]
    match t, E, η, hE, hη, q, p, i, hip with
    | 0, _, _, _, _, q, _, _, _ => exact q.elim0
    | 1, _, _, _, _, _, p, i, hip => exact absurd (Subsingleton.elim i p) hip
    | m + 2, E, η, hE, hη, q, p, i, hip => exact Formalism.FourierDecayAlt.P.QuantumMinorCommutation.minorCov_succ E η hE hη u q p i hip
end Formalism.FourierDecayAlt.P
