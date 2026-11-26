-- Prove2me | solution 1 for FirstPassageLinearTransport.scaledReverseLoss_le_half_time
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:29:54.905999+00:00
-- url     : https://prove2.me/submissions/4d614361-a6a6-42c6-80be-e324f46284fe

import Definitions.Def_FirstPassageLinearTransport_LossTransport
import Definitions.Def_FirstPassageLinearTransport_RawDynamics
import Definitions.Def_FirstPassageLinearTransport_NestedRecertification
import Theorems.Thm_FirstPassageLinearTransport_mem_dyadicShell
import Theorems.Thm_FirstPassageLinearTransport_mem_lossFilteredTaggedFiber
import Theorems.Thm_FirstPassageLinearTransport_mem_lossFilteredTransportedSources
import Theorems.Thm_FirstPassageLinearTransport_mem_taggedFiber
import Theorems.Thm_FirstPassageLinearTransport_mem_transportedSources
import Theorems.Thm_FirstPassageLinearTransport_oddCount_zero
import Theorems.Thm_FirstPassageLinearTransport_orbit_zero
import Theorems.Thm_FirstPassageLinearTransport_parityBit_zero
import Theorems.Thm_FirstPassageLinearTransport_rawOrbit_zero
import Theorems.Thm_FirstPassageLinearTransport_reverseLoss_le_firstPassage
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
    {Y n h : ℕ} (hY : 0 < Y) (hfp : IsFirstPassage Y n h) :
    scaledReverseLoss Y n h ≤ (h : ℚ) / 2 := by
  have hsum :
      reverseLossTotal n h ≤ (h : ℚ) / (2 * (Y : ℚ)) := by
    unfold reverseLossTotal
    calc
      ∑ i ∈ Finset.range h, reverseLoss n i ≤
          ∑ _i ∈ Finset.range h, (1 / (2 * (Y : ℚ)) : ℚ) := by
            apply Finset.sum_le_sum
            intro i hi
            exact reverseLoss_le_firstPassage hY hfp
              (Finset.mem_range.mp hi)
      _ = (h : ℚ) / (2 * (Y : ℚ)) := by
        simp
        ring
  have hYQ : (0 : ℚ) ≤ (Y : ℚ) := by positivity
  unfold scaledReverseLoss
  calc
    (Y : ℚ) * reverseLossTotal n h ≤
        (Y : ℚ) * ((h : ℚ) / (2 * (Y : ℚ))) :=
      mul_le_mul_of_nonneg_left hsum hYQ
    _ = (h : ℚ) / 2 := by
      have hYne : (Y : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hY)
      field_simp [hYne]
end FirstPassageLinearTransport
