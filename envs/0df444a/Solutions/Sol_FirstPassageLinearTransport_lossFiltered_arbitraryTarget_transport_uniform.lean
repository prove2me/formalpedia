-- Prove2me | solution 1 for FirstPassageLinearTransport.lossFiltered_arbitraryTarget_transport_uniform
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:41:46.587164+00:00
-- url     : https://prove2.me/submissions/4fe07b10-b885-4710-947b-aeb29632b8c0

import Definitions.Def_FirstPassageLinearTransport_Transport
import Definitions.Def_FirstPassageLinearTransport_LossTransport
import Theorems.Thm_FirstPassageLinearTransport_mem_lossFilteredTaggedFiber
import Theorems.Thm_FirstPassageLinearTransport_mem_lossFilteredTransportedSources
import Theorems.Thm_FirstPassageLinearTransport_lossFiltered_arbitraryTarget_transport
import Theorems.Thm_FirstPassageLinearTransport_mem_dyadicShell
import Theorems.Thm_FirstPassageLinearTransport_mem_taggedFiber
import Theorems.Thm_FirstPassageLinearTransport_mem_transportedSources
import Theorems.Thm_FirstPassageLinearTransport_oddCount_zero
import Theorems.Thm_FirstPassageLinearTransport_orbit_zero
import Theorems.Thm_FirstPassageLinearTransport_parityBit_zero
import Theorems.Thm_FirstPassageLinearTransport_shortcut_zero
attribute [local simp] FirstPassageLinearTransport.mem_dyadicShell
attribute [local simp] FirstPassageLinearTransport.mem_taggedFiber
attribute [local simp] FirstPassageLinearTransport.mem_transportedSources
attribute [local simp] FirstPassageLinearTransport.oddCount_zero
attribute [local simp] FirstPassageLinearTransport.orbit_zero
attribute [local simp] FirstPassageLinearTransport.parityBit_zero
attribute [local simp] FirstPassageLinearTransport.shortcut_zero


attribute [local simp] FirstPassageLinearTransport.mem_lossFilteredTaggedFiber
attribute [local simp] FirstPassageLinearTransport.mem_lossFilteredTransportedSources

set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution
    {M Y H : ℕ} (B : Finset ℕ) {D : ℚ}
    (hY : 0 < Y) (hD : 0 ≤ D)
    (hsmall : D / (Y : ℚ) ≤ 1 / 3) (hYM : Y < 2 ^ M) :
    ((lossFilteredTransportedSources M Y H B D).card : ℚ) ≤
      (H : ℚ) * (1 + 3 * D) * (2 : ℚ) ^ M / (Y : ℚ) *
        (B.card : ℚ) := by
  have hYQ : (0 : ℚ) < (Y : ℚ) := by exact_mod_cast hY
  have hYMq : (Y : ℚ) < (2 : ℚ) ^ M := by exact_mod_cast hYM
  have hratio : (1 : ℚ) ≤ (2 : ℚ) ^ M / (Y : ℚ) := by
    apply (le_div_iff₀ hYQ).2
    simpa using hYMq.le
  have hK :
      1 + 3 * D * (2 : ℚ) ^ M / (Y : ℚ) ≤
        (1 + 3 * D) * (2 : ℚ) ^ M / (Y : ℚ) := by
    calc
      1 + 3 * D * (2 : ℚ) ^ M / (Y : ℚ) ≤
          (2 : ℚ) ^ M / (Y : ℚ) +
            3 * D * (2 : ℚ) ^ M / (Y : ℚ) :=
        by
          simpa [add_comm] using
            add_le_add_right hratio
              (3 * D * (2 : ℚ) ^ M / (Y : ℚ))
      _ = (1 + 3 * D) * (2 : ℚ) ^ M / (Y : ℚ) := by ring
  have hbase := lossFiltered_arbitraryTarget_transport
    (M := M) (Y := Y) (H := H) (D := D) B hY hD hsmall
  have hcoef : 0 ≤ (H : ℚ) * (B.card : ℚ) := by positivity
  have hmul := mul_le_mul_of_nonneg_left hK hcoef
  calc
    ((lossFilteredTransportedSources M Y H B D).card : ℚ) ≤
        (H : ℚ) *
          (1 + 3 * D * (2 : ℚ) ^ M / (Y : ℚ)) *
            (B.card : ℚ) := hbase
    _ = ((H : ℚ) * (B.card : ℚ)) *
          (1 + 3 * D * (2 : ℚ) ^ M / (Y : ℚ)) := by ring
    _ ≤ ((H : ℚ) * (B.card : ℚ)) *
          ((1 + 3 * D) * (2 : ℚ) ^ M / (Y : ℚ)) := hmul
    _ = (H : ℚ) * (1 + 3 * D) * (2 : ℚ) ^ M / (Y : ℚ) *
          (B.card : ℚ) := by ring
end FirstPassageLinearTransport
