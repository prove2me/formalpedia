-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.phase_critical_points
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:50:33.40494+00:00
-- url     : https://prove2.me/submissions/37b9c891-eb33-4e0f-8d65-e5dc9b840326

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelNonzeroModulusDeterminantEq
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralLatticeRefinementIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GaussSumModulusOfLattice
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_blk_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_val
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x5_mv_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.DoubleCosetMeasures.P.Phase.blk_revF
attribute [local simp] Formalism.DoubleCosetMeasures.P.Phase.revF_revF
attribute [local simp] Formalism.DoubleCosetMeasures.P.Phase.revF_val
attribute [local simp] Formalism.FourierDecayAlt.P.A5x5.mv_apply



set_option autoImplicit false
noncomputable section
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.A6.CritPoints := by
  intro K _ m hm D' x
  constructor
  · intro h
    obtain ⟨k0⟩ : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
    have hx : ∀ k, x k = x k0 := by
      intro k
      have := (h k).trans (h k0).symm
      exact mul_right_cancel this
    refine ⟨x k0, hx, ?_⟩
    have := h k0
    rw [Finset.prod_congr rfl (fun j _ => hx j)] at this
    simpa [pow_succ, mul_comm] using this
  · rintro ⟨z, hz, hD⟩ k
    rw [Finset.prod_congr rfl (fun j _ => hz j), hz k]
    simpa [pow_succ, mul_comm] using hD
end Formalism.FourierDecayAlt.P
