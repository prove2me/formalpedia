-- Prove2me | solution 1 for FirstPassageLinearTransport.ShrinkingRecertificationRun.certified_endpoint_shell_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:49:50.327726+00:00
-- url     : https://prove2.me/submissions/d211d6d7-8a6d-4f08-b0b3-e091b4ab3928

import Definitions.Def_FirstPassageLinearTransport_ShrinkingBarrierCore
import Definitions.Def_FirstPassageLinearTransport_TwoRegimeClock
import Definitions.Def_FirstPassageLinearTransport_ShrinkingBarrierRun
import Theorems.Thm_FirstPassageLinearTransport_ShrinkingRecertificationRun_elapsed_pos
import Theorems.Thm_FirstPassageLinearTransport_ShrinkingRecertificationRun_currentRank_pos
import Theorems.Thm_FirstPassageLinearTransport_ShrinkingRecertificationRun_directFirstPassage
import Theorems.Thm_FirstPassageLinearTransport_CertifiedRankChain_directFirstPassage
import Theorems.Thm_FirstPassageLinearTransport_RecertificationRun_currentRank_pos
import Theorems.Thm_FirstPassageLinearTransport_RecertificationRun_elapsed_pos
import Theorems.Thm_FirstPassageLinearTransport_certified_landing_mem_lower_shell
import Theorems.Thm_FirstPassageLinearTransport_firstPassage_band
import Theorems.Thm_FirstPassageLinearTransport_log_two_eq_of_mem_dyadicShell


set_option autoImplicit true
open FirstPassageLinearTransport
open scoped Real
noncomputable section
namespace FirstPassageLinearTransport
namespace ShrinkingRecertificationRun
theorem _root_.solution
    {P : ShrinkingBarrierRunData} {M S n elapsed q m : ℕ}
    (hrun : ShrinkingRecertificationRun P M S n elapsed q)
    {t : ℝ} (htA : t < a0)
    (hgood : orbit elapsed n ∈ initialWindowGood t)
    (hshell : orbit elapsed n ∈ dyadicShell m) :
    m = q - 1 := by
  have hband := firstPassage_band hrun.elapsed_pos hrun.directFirstPassage
  have hlowerBand : 2 ^ (q - 1) < orbit elapsed n := by
    have hmul : 2 ^ (q - 1) * 2 < orbit elapsed n * 2 := by
      calc
        2 ^ (q - 1) * 2 = 2 ^ ((q - 1) + 1) := by rw [pow_succ]
        _ = 2 ^ q := by rw [Nat.sub_add_cancel hrun.currentRank_pos]
        _ < 2 * orbit elapsed n := hband.1
        _ = orbit elapsed n * 2 := by omega
    exact lt_of_mul_lt_mul_right hmul (by norm_num)
  have hlower := certified_landing_mem_lower_shell hrun.currentRank_pos htA
    ⟨hlowerBand, hband.2⟩ hgood
  have hlogm := log_two_eq_of_mem_dyadicShell hshell
  have hlogq := log_two_eq_of_mem_dyadicShell hlower
  omega
end ShrinkingRecertificationRun
end FirstPassageLinearTransport
