-- Prove2me | solution 1 for FirstPassageLinearTransport.CertifiedRankChain.scaledReverseLoss_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:48:24.122082+00:00
-- url     : https://prove2.me/submissions/4aedf867-b2bb-47f7-90bf-223210365e66

import Definitions.Def_FirstPassageLinearTransport_NestedRecertification
import Definitions.Def_FirstPassageLinearTransport_RankScaledLoss
import Theorems.Thm_FirstPassageLinearTransport_scaledReverseLoss_rank_step
import Theorems.Thm_FirstPassageLinearTransport_mem_dyadicShell
import Theorems.Thm_FirstPassageLinearTransport_mem_lossFilteredTaggedFiber
import Theorems.Thm_FirstPassageLinearTransport_mem_lossFilteredTransportedSources
import Theorems.Thm_FirstPassageLinearTransport_mem_taggedFiber
import Theorems.Thm_FirstPassageLinearTransport_mem_transportedSources
import Theorems.Thm_FirstPassageLinearTransport_oddCount_zero
import Theorems.Thm_FirstPassageLinearTransport_orbit_zero
import Theorems.Thm_FirstPassageLinearTransport_parityBit_zero
import Theorems.Thm_FirstPassageLinearTransport_rawOrbit_zero
import Theorems.Thm_FirstPassageLinearTransport_scaledReverseLoss_le_half_time
import Theorems.Thm_FirstPassageLinearTransport_shortcut_zero
attribute [local simp] FirstPassageLinearTransport.mem_dyadicShell
attribute [local simp] FirstPassageLinearTransport.mem_lossFilteredTaggedFiber
attribute [local simp] FirstPassageLinearTransport.mem_lossFilteredTransportedSources
attribute [local simp] FirstPassageLinearTransport.mem_taggedFiber
attribute [local simp] FirstPassageLinearTransport.mem_transportedSources
attribute [local simp] FirstPassageLinearTransport.oddCount_zero
attribute [local simp] FirstPassageLinearTransport.orbit_zero
attribute [local simp] FirstPassageLinearTransport.parityBit_zero
attribute [local simp] FirstPassageLinearTransport.rawOrbit_zero
attribute [local simp] FirstPassageLinearTransport.shortcut_zero



set_option autoImplicit true
open FirstPassageLinearTransport
noncomputable section
namespace FirstPassageLinearTransport
namespace CertifiedRankChain
theorem _root_.solution
    {r : ℚ} (hr : 0 < r) {n t q : ℕ}
    (hchain : CertifiedRankChain r n t q) :
    scaledReverseLoss (2 ^ q) n t ≤ ((q + 2 : ℕ) : ℚ) / r := by
  induction hchain with
  | @first q m h hfp hhm hm =>
      have hY : 0 < 2 ^ q := by positivity
      have hlocal := scaledReverseLoss_le_half_time hY hfp
      have hhmQ : (h : ℚ) ≤ (m : ℚ) := by exact_mod_cast hhm
      calc
        scaledReverseLoss (2 ^ q) n h ≤ (h : ℚ) / 2 := hlocal
        _ ≤ (m : ℚ) / 2 := by linarith
        _ ≤ (((q + 1 : ℕ) : ℚ) / r) / 2 := by
          exact div_le_div_of_nonneg_right hm (by norm_num)
        _ ≤ ((q + 2 : ℕ) : ℚ) / r := by
          have hq :
              ((q + 1 : ℕ) : ℚ) / 2 ≤ ((q + 2 : ℕ) : ℚ) := by
            push_cast
            have hq0 : (0 : ℚ) ≤ q := by positivity
            linarith
          have hqR := (div_le_div_iff_of_pos_right hr).2 hq
          simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hqR
  | @next t qprev q m h hchain hgap hfp hhm hm ih =>
      let d : ℕ := qprev - q - 1
      have hqprev : qprev = q + d + 1 := by
        dsimp [d]
        omega
      have hprevious :
          scaledReverseLoss (2 ^ (q + d + 1)) n t ≤
            ((q + d + 3 : ℕ) : ℚ) / r := by
        rw [hqprev] at ih
        convert ih using 1
      exact scaledReverseLoss_rank_step hr hprevious hfp hhm hm
end CertifiedRankChain
end FirstPassageLinearTransport
