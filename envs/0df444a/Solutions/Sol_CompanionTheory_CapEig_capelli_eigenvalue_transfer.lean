-- Prove2me | solution 1 for CompanionTheory.CapEig.capelli_eigenvalue_transfer
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T06:35:32.104751+00:00
-- url     : https://prove2.me/submissions/4f27dbec-224b-49f4-a800-681a4332389b

import Definitions.Def_CompanionTheory_AutomorphicTheory_ZuckermanCommutation_CapelliEigenvalues_FunAct
import Definitions.Def_CompanionTheory_AutomorphicTheory_SchurLimitBounds_ZuckermanDuality_ZuckDualTOfZuckDual
import Definitions.Def_CompanionTheory_AutomorphicTheory_ZuckermanCommutation_CapelliEigenvalues_CoefEig
import Theorems.Thm_CompanionTheory_CapEig_qminorOp_cast

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix PI.UpqRep Formalism.FourierDecayAlt
open scoped InnerProductSpace
noncomputable section
open CompanionTheory CompanionTheory.CapEig
namespace CompanionTheory.CapEig
theorem _root_.solution : CompanionTheory.LimBd.Main.CVBridge := by
  intro k r E _ _ Y F
  unfold Q.CV Q.capL PI.CapelliEig.capC Formalism.QuantumDeterminants.capelliH Formalism.QuantumDeterminants.qdetOp
  have hm : Q.mdim k r 0 = 2 * r + k + 1 := by simp [Q.mdim]
  have hu : Q.uC k r 0 Y = Y + ((2 * r + k : ℕ) : ℂ) / 2 := by
    unfold Q.uC; rw [hm]; push_cast; ring
  rw [hu]
  exact qminorOp_cast _ hm _ (fun j => by simp [Q.posL]) _ _
end CompanionTheory.CapEig
