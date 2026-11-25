-- Prove2me | solution 1 for Formalism.BranchingDeterminantCap.passageLat_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T01:47:19.096488+00:00
-- url     : https://prove2.me/submissions/94b96408-2fcc-4e82-9020-86a0e61ecd9d

import Mathlib
import Definitions.Def_Formalism_BranchSandwichDivisors_StatementL
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_TransferMean
import Definitions.Def_Formalism_MeanHeightDescent_AverageDegreeBounds_GoodBadCut
import Definitions.Def_Formalism_HarderNarasimhan_ShiftInvariance
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_Transfer
import Theorems.Thm_Formalism_BranchingDeterminantCap_PrismTransfer_degD_le_muMax
import Theorems.Thm_Formalism_BranchingDeterminantCap_meanTransferBound
import Theorems.Thm_Formalism_ExtensionFiltration_HermitianIdempotentFrameLemmas_rkK_ne_zero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField
open scoped Matrix
noncomputable section
open Formalism Formalism.BranchingDeterminantCap
open Formalism.HN
open PrismTransfer
namespace Formalism.BranchingDeterminantCap
theorem _root_.solution (hLC : LevelCompare) : PassageLat := by
  intro K V ι _ _ _ _ _ _ _ _ _ _ b X hX S _ Rs nS latticeAtBaseLevel RPs R0 R1 G h0 h1 nbar de HH0 hP0 hPs hR0 hR1
    hh0 hh0G hh1 hh1G hR0le hR0s hR1le hR1s hRs hrk0 hrks hdegs hdeg0 hnbar hde0 hde hnS hHH
  obtain ⟨a0, a0'⟩ := hLC K V ι b X hX latticeAtBaseLevel R0 h0 hP0 hR0 hh0 hR0le hR0s
  obtain ⟨a1, _⟩ := hLC K V ι b X hX RPs R1 h1 hPs hR1 hh1 hR1le hR1s
  have hl0 : Real.log h0 ≤ Real.log G :=
    Real.log_le_log (by exact_mod_cast hh0) (by exact_mod_cast hh0G)
  have hl1 : Real.log h1 ≤ Real.log G :=
    Real.log_le_log (by exact_mod_cast hh1) (by exact_mod_cast hh1G)
  have hla : 0 ≤ Real.log G := Real.log_natCast_nonneg G
  have hP0ne : latticeAtBaseLevel ≠ ⊥ := fun h => hR0 (le_bot_iff.1 (h ▸ hR0le))
  have hrkpos : (0 : ℝ) < (rkK latticeAtBaseLevel : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Formalism.ExtensionFiltration.HermitianIdempotentFrameLemmas.rkK_ne_zero b latticeAtBaseLevel hP0ne)
  have key := (meanTransferBound S (fun s => (rkK (Rs s) : ℝ)) (fun s => (nS s : ℝ))
    (fun s => degD b X (Rs s)) nbar de (Real.log G) 1 HH0 (muDef b X latticeAtBaseLevel) (muDef b X RPs)
    (muDef b (scaleFrame (Real.sqrt h0) X) R0) (muDef b (scaleFrame (Real.sqrt h1) X) R1)
    hnbar hde0 hde hla zero_le_one (fun s => Nat.cast_nonneg _) (by rw [← hrk0]; exact hrkpos) hnS
    (by linarith) (by linarith)
    (fun s => by
      have h5 := degD_le_muMax b X hX (Rs s) latticeAtBaseLevel hP0 (hRs s)
      have h6 : muMaxDef b X latticeAtBaseLevel ≤ HH0 + 1 * Real.log G := by
        have := (abs_le.1 a0').1
        linarith
      exact h5.trans (mul_le_mul_of_nonneg_left h6 (Nat.cast_nonneg _)))
    (by
      rw [← hrks]
      have : muDef b X RPs * (rkK RPs : ℝ) = degD b X RPs := by unfold degD; ring
      rw [this]; exact hdegs)
    (by
      rw [← hrk0]
      have : muDef b X latticeAtBaseLevel * (rkK latticeAtBaseLevel : ℝ) = degD b X latticeAtBaseLevel := by unfold degD; ring
      rw [this]; exact hdeg0)).2
  have e1 : (2 * (1 : ℝ) + 2) = 4 := by norm_num
  have e2 : (2 * (1 : ℝ) + 21 / 2) = 25 / 2 := by norm_num
  rw [e1, e2] at key
  exact key
end Formalism.BranchingDeterminantCap
