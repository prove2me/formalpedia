-- Prove2me | solution 1 for FirstPassageLinearTransport.TimeoutRecertificationRun.endpoint_mem_timeoutHighLandingBad
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:11:02.506563+00:00
-- url     : https://prove2.me/submissions/4afd42ad-a58b-4fcf-87aa-f7bfb2528110

import Definitions.Def_FirstPassageLinearTransport_TimeoutEnvelope
import Definitions.Def_FirstPassageLinearTransport_TimeoutExecution
import Theorems.Thm_FirstPassageLinearTransport_RecertificationRun_currentRank_pos
import Theorems.Thm_FirstPassageLinearTransport_ShrinkingRecertificationRun_currentRank_pos
import Theorems.Thm_FirstPassageLinearTransport_TimeoutRecertificationRun_currentRank_pos
import Theorems.Thm_FirstPassageLinearTransport_TimeoutRecertificationRun_landingBand
import Theorems.Thm_FirstPassageLinearTransport_mem_landingBad
attribute [local simp] FirstPassageLinearTransport.mem_landingBad



set_option autoImplicit true
open FirstPassageLinearTransport
noncomputable section
namespace FirstPassageLinearTransport
namespace TimeoutRecertificationRun
theorem _root_.solution
    {P : TimeoutHighRunData} {K₀ : ℝ}
    {L M S n elapsed q : ℕ}
    (hrun : TimeoutRecertificationRun P K₀ L M S n elapsed q)
    (hbad : orbit elapsed n ∉
      initialWindowGood (timeoutHighTargetTolerance P M q)) :
    orbit elapsed n ∈
      landingBad q (timeoutHighTargetTolerance P M q) := by
  have hband := hrun.landingBand
  have hq := hrun.currentRank_pos
  apply mem_landingBad.mpr
  refine ⟨?_, hband.2, hbad⟩
  have hmul : 2 ^ (q - 1) * 2 < orbit elapsed n * 2 := by
    calc
      2 ^ (q - 1) * 2 = 2 ^ ((q - 1) + 1) := by rw [pow_succ]
      _ = 2 ^ q := by rw [Nat.sub_add_cancel hq]
      _ < 2 * orbit elapsed n := hband.1
      _ = orbit elapsed n * 2 := by omega
  exact lt_of_mul_lt_mul_right hmul (by norm_num)
end TimeoutRecertificationRun
end FirstPassageLinearTransport
