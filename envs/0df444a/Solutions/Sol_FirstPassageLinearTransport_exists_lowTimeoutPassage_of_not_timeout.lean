-- Prove2me | solution 1 for FirstPassageLinearTransport.exists_lowTimeoutPassage_of_not_timeout
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:08:09.190213+00:00
-- url     : https://prove2.me/submissions/0e68c8a6-22dd-497c-86d6-829e7f7b2a72

import Definitions.Def_FirstPassageLinearTransport_TimeoutDensity
import Definitions.Def_FirstPassageLinearTransport_ShrinkingBarrierRun
import Definitions.Def_FirstPassageLinearTransport_RankScaledLoss
import Definitions.Def_FirstPassageLinearTransport_TimeoutRun

set_option autoImplicit true
open FirstPassageLinearTransport
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution
    {K₀ : ℝ} {L m x : ℕ}
    (hnot : ¬LowStageTimeout K₀ L m x) :
    Nonempty (LowTimeoutPassage K₀ L m x) := by
  classical
  rw [LowStageTimeout] at hnot
  push_neg at hnot
  obtain ⟨j, hj⟩ := hnot
  have hexists :
      ∃ h : ℕ,
        h ≤ m ∧ orbit h x ≤ 2 ^ timeoutTargetRank K₀ L m :=
    ⟨j, by omega, by omega⟩
  let h := Nat.find hexists
  have hspec := Nat.find_spec hexists
  refine ⟨⟨h, hspec.1, hspec.2, ?_⟩⟩
  intro i hi
  by_contra hle
  have hiTarget : orbit i x ≤ 2 ^ timeoutTargetRank K₀ L m :=
    Nat.le_of_not_gt hle
  exact Nat.find_min hexists hi ⟨hi.le.trans hspec.1, hiTarget⟩
end FirstPassageLinearTransport
