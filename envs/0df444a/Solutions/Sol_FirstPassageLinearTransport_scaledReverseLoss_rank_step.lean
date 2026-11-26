-- Prove2me | solution 1 for FirstPassageLinearTransport.scaledReverseLoss_rank_step
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:44:29.460657+00:00
-- url     : https://prove2.me/submissions/164fbecd-42e1-415d-b42a-628b6fe98fda

import Definitions.Def_FirstPassageLinearTransport_NestedRecertification
import Definitions.Def_FirstPassageLinearTransport_RankScaledLoss
import Theorems.Thm_FirstPassageLinearTransport_rankScaledBudget_step
import Theorems.Thm_FirstPassageLinearTransport_mem_dyadicShell
import Theorems.Thm_FirstPassageLinearTransport_mem_lossFilteredTaggedFiber
import Theorems.Thm_FirstPassageLinearTransport_mem_lossFilteredTransportedSources
import Theorems.Thm_FirstPassageLinearTransport_mem_taggedFiber
import Theorems.Thm_FirstPassageLinearTransport_mem_transportedSources
import Theorems.Thm_FirstPassageLinearTransport_oddCount_zero
import Theorems.Thm_FirstPassageLinearTransport_orbit_zero
import Theorems.Thm_FirstPassageLinearTransport_parityBit_zero
import Theorems.Thm_FirstPassageLinearTransport_rawOrbit_zero
import Theorems.Thm_FirstPassageLinearTransport_scaledReverseLoss_add_rescaled
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
theorem _root_.solution
    {q d m n k h : ℕ} {r : ℚ}
    (hr : 0 < r)
    (hprevious :
      scaledReverseLoss (2 ^ (q + d + 1)) n k ≤
        ((q + d + 3 : ℕ) : ℚ) / r)
    (hlocalFP : IsFirstPassage (2 ^ q) (orbit k n) h)
    (hhm : h ≤ m)
    (hm : (m : ℚ) ≤ ((q + 1 : ℕ) : ℚ) / r) :
    scaledReverseLoss (2 ^ q) n (k + h) ≤
      ((q + 2 : ℕ) : ℚ) / r := by
  have hYhi : 0 < 2 ^ (q + d + 1) := by positivity
  have hYlo : 0 < 2 ^ q := by positivity
  have hadd := scaledReverseLoss_add_rescaled
    (Ylo := 2 ^ q) (Yhi := 2 ^ (q + d + 1)) n k h hYhi
  have hratio :
      ((2 ^ q : ℕ) : ℚ) / ((2 ^ (q + d + 1) : ℕ) : ℚ) =
        1 / (2 : ℚ) ^ (d + 1) := by
    push_cast
    rw [show q + d + 1 = q + (d + 1) by omega, pow_add]
    have hp : (2 : ℚ) ^ q ≠ 0 := pow_ne_zero _ (by norm_num)
    field_simp [hp]
  have hlocal0 := scaledReverseLoss_le_half_time hYlo hlocalFP
  have hhq : (h : ℚ) ≤ (m : ℚ) := by exact_mod_cast hhm
  have hlocal :
      scaledReverseLoss (2 ^ q) (orbit k n) h ≤
        ((q + 1 : ℕ) : ℚ) / (2 * r) := by
    calc
      scaledReverseLoss (2 ^ q) (orbit k n) h ≤ (h : ℚ) / 2 := hlocal0
      _ ≤ (m : ℚ) / 2 := by linarith
      _ ≤ ((q + 1 : ℕ) : ℚ) / (2 * r) := by
        have hhalf := mul_le_mul_of_nonneg_left hm
          (by norm_num : (0 : ℚ) ≤ 1 / 2)
        simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hhalf
  rw [hadd, hratio]
  exact rankScaledBudget_step hr hprevious hlocal
end FirstPassageLinearTransport
