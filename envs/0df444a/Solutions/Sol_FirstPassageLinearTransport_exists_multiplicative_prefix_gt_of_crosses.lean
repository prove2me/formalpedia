-- Prove2me | solution 1 for FirstPassageLinearTransport.exists_multiplicative_prefix_gt_of_crosses
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:15:59.956778+00:00
-- url     : https://prove2.me/submissions/b4185f3b-baed-4b7f-8e81-0de664a89270

import Definitions.Def_FirstPassageLinearTransport_NaturalDensityDescent
import Definitions.Def_FirstPassageLinearTransport_TimeoutDensity
import Definitions.Def_FirstPassageLinearTransport_RawDynamics
import Definitions.Def_FirstPassageLinearTransport_OrbitCeiling
import Theorems.Thm_FirstPassageLinearTransport_ballotMultiplier_boolParityWord_zero
import Theorems.Thm_FirstPassageLinearTransport_ballotWordValue_cons
import Theorems.Thm_FirstPassageLinearTransport_ballotWordValue_scale
import Theorems.Thm_FirstPassageLinearTransport_ballotWordValue_zero
import Theorems.Thm_FirstPassageLinearTransport_boolParityCode_eq_word
import Theorems.Thm_FirstPassageLinearTransport_boolParityWord_tail
import Theorems.Thm_FirstPassageLinearTransport_bootstrapC_zero
import Theorems.Thm_FirstPassageLinearTransport_bootstrapD_zero
import Theorems.Thm_FirstPassageLinearTransport_bootstrapSet_zero
import Theorems.Thm_FirstPassageLinearTransport_card_boolSupport_cons
import Theorems.Thm_FirstPassageLinearTransport_mem_dyadicShell
import Theorems.Thm_FirstPassageLinearTransport_mem_prefixBad
import Theorems.Thm_FirstPassageLinearTransport_mem_taggedFiber
import Theorems.Thm_FirstPassageLinearTransport_mem_transportedSources
import Theorems.Thm_FirstPassageLinearTransport_oddCount_succ_shift
import Theorems.Thm_FirstPassageLinearTransport_oddCount_zero
import Theorems.Thm_FirstPassageLinearTransport_orbit_zero
import Theorems.Thm_FirstPassageLinearTransport_parityBit_zero
import Theorems.Thm_FirstPassageLinearTransport_rawOrbit_zero
import Theorems.Thm_FirstPassageLinearTransport_shortcut_zero
import Theorems.Thm_FirstPassageLinearTransport_stageClock_zero
import Theorems.Thm_FirstPassageLinearTransport_stageOrbit_zero
import Theorems.Thm_FirstPassageLinearTransport_stoppedBallotValue_cons
attribute [local simp] FirstPassageLinearTransport.ballotWordValue_cons
attribute [local simp] FirstPassageLinearTransport.ballotWordValue_scale
attribute [local simp] FirstPassageLinearTransport.ballotWordValue_zero
attribute [local simp] FirstPassageLinearTransport.boolParityCode_eq_word
attribute [local simp] FirstPassageLinearTransport.bootstrapC_zero
attribute [local simp] FirstPassageLinearTransport.bootstrapD_zero
attribute [local simp] FirstPassageLinearTransport.bootstrapSet_zero
attribute [local simp] FirstPassageLinearTransport.card_boolSupport_cons
attribute [local simp] FirstPassageLinearTransport.mem_dyadicShell
attribute [local simp] FirstPassageLinearTransport.mem_prefixBad
attribute [local simp] FirstPassageLinearTransport.mem_taggedFiber
attribute [local simp] FirstPassageLinearTransport.mem_transportedSources
attribute [local simp] FirstPassageLinearTransport.oddCount_zero
attribute [local simp] FirstPassageLinearTransport.orbit_zero
attribute [local simp] FirstPassageLinearTransport.parityBit_zero
attribute [local simp] FirstPassageLinearTransport.rawOrbit_zero
attribute [local simp] FirstPassageLinearTransport.shortcut_zero
attribute [local simp] FirstPassageLinearTransport.stageClock_zero
attribute [local simp] FirstPassageLinearTransport.stageOrbit_zero
attribute [local simp] FirstPassageLinearTransport.stoppedBallotValue_cons



set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution :
    ∀ {r n : ℕ} {u z : ℝ},
      crossesMultiplicativeFrom u r z (boolParityWord r n) →
      ∃ H : ℕ, H ≤ r ∧
        u < z * ((3 : ℝ) ^ oddCount n H / (2 : ℝ) ^ H) := by
  intro r
  induction r with
  | zero =>
      intro n u z hcross
      refine ⟨0, by omega, ?_⟩
      simpa [crossesMultiplicativeFrom] using hcross
  | succ r ih =>
      intro n u z hcross
      have hdecomp :
          u < z ∨
            crossesMultiplicativeFrom u r
              (z * ballotMultiplier (boolParityWord (r + 1) n 0))
              (boolParityWord r (shortcut n)) := by
        have hraw :
            u < z ∨
              crossesMultiplicativeFrom u r
                (z * ballotMultiplier (boolParityWord (r + 1) n 0))
                (fun i => boolParityWord (r + 1) n i.succ) := by
          simpa [crossesMultiplicativeFrom] using hcross
        simpa [boolParityWord_tail] using hraw
      rcases hdecomp with hcurrent | htail
      · exact ⟨0, by omega, by simpa using hcurrent⟩
      · obtain ⟨H, hHr, hchild⟩ := ih htail
        refine ⟨H + 1, by omega, ?_⟩
        rw [ballotMultiplier_boolParityWord_zero] at hchild
        rw [oddCount_succ_shift, pow_add, pow_succ]
        convert hchild using 1 <;> ring
end FirstPassageLinearTransport
