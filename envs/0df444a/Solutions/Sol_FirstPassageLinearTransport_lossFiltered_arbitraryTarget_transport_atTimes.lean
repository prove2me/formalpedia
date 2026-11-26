-- Prove2me | solution 1 for FirstPassageLinearTransport.lossFiltered_arbitraryTarget_transport_atTimes
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:41:01.757986+00:00
-- url     : https://prove2.me/submissions/0222c5a6-b92e-44ff-9338-75d9281ce5b7

import Definitions.Def_FirstPassageLinearTransport_LossTransport
import Definitions.Def_FirstPassageLinearTransport_TimeSupportTransport
import Theorems.Thm_FirstPassageLinearTransport_mem_lossFilteredTransportedSourcesAtTimes
import Theorems.Thm_FirstPassageLinearTransport_card_biUnion_le_sum
import Theorems.Thm_FirstPassageLinearTransport_lossFilteredTaggedFiber_bound
import Theorems.Thm_FirstPassageLinearTransport_mem_dyadicShell
import Theorems.Thm_FirstPassageLinearTransport_mem_lossFilteredTaggedFiber
import Theorems.Thm_FirstPassageLinearTransport_mem_lossFilteredTransportedSources
import Theorems.Thm_FirstPassageLinearTransport_mem_taggedFiber
import Theorems.Thm_FirstPassageLinearTransport_mem_transportedSources
import Theorems.Thm_FirstPassageLinearTransport_oddCount_zero
import Theorems.Thm_FirstPassageLinearTransport_orbit_zero
import Theorems.Thm_FirstPassageLinearTransport_parityBit_zero
import Theorems.Thm_FirstPassageLinearTransport_shortcut_zero
attribute [local simp] FirstPassageLinearTransport.mem_dyadicShell
attribute [local simp] FirstPassageLinearTransport.mem_lossFilteredTaggedFiber
attribute [local simp] FirstPassageLinearTransport.mem_lossFilteredTransportedSources
attribute [local simp] FirstPassageLinearTransport.mem_taggedFiber
attribute [local simp] FirstPassageLinearTransport.mem_transportedSources
attribute [local simp] FirstPassageLinearTransport.oddCount_zero
attribute [local simp] FirstPassageLinearTransport.orbit_zero
attribute [local simp] FirstPassageLinearTransport.parityBit_zero
attribute [local simp] FirstPassageLinearTransport.shortcut_zero


attribute [local simp] FirstPassageLinearTransport.mem_lossFilteredTransportedSourcesAtTimes

set_option autoImplicit true
open FirstPassageLinearTransport
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution
    {M Y : ℕ} (times B : Finset ℕ) {D : ℚ}
    (hY : 0 < Y) (hD : 0 ≤ D)
    (hsmall : D / (Y : ℚ) ≤ 1 / 3) :
    ((lossFilteredTransportedSourcesAtTimes M Y times B D).card : ℚ) ≤
      (times.card : ℚ) *
        (1 + 3 * D * (2 : ℚ) ^ M / (Y : ℚ)) * (B.card : ℚ) := by
  classical
  have houter := card_biUnion_le_sum times fun h =>
    B.biUnion fun y => lossFilteredTaggedFiber M Y h y D
  have hcardNat :
      (lossFilteredTransportedSourcesAtTimes M Y times B D).card ≤
        ∑ h ∈ times, ∑ y ∈ B,
          (lossFilteredTaggedFiber M Y h y D).card := by
    unfold lossFilteredTransportedSourcesAtTimes
    calc
      (times.biUnion fun h =>
          B.biUnion fun y => lossFilteredTaggedFiber M Y h y D).card ≤
          ∑ h ∈ times,
            (B.biUnion fun y => lossFilteredTaggedFiber M Y h y D).card :=
        houter
      _ ≤ ∑ h ∈ times, ∑ y ∈ B,
          (lossFilteredTaggedFiber M Y h y D).card := by
        apply Finset.sum_le_sum
        intro h _hh
        exact card_biUnion_le_sum B fun y =>
          lossFilteredTaggedFiber M Y h y D
  have hcardQ :
      ((lossFilteredTransportedSourcesAtTimes M Y times B D).card : ℚ) ≤
        ∑ h ∈ times, ∑ y ∈ B,
          ((lossFilteredTaggedFiber M Y h y D).card : ℚ) := by
    exact_mod_cast hcardNat
  let K : ℚ := 1 + 3 * D * (2 : ℚ) ^ M / (Y : ℚ)
  calc
    ((lossFilteredTransportedSourcesAtTimes M Y times B D).card : ℚ) ≤
        ∑ h ∈ times, ∑ y ∈ B,
          ((lossFilteredTaggedFiber M Y h y D).card : ℚ) := hcardQ
    _ ≤ ∑ _h ∈ times, ∑ _y ∈ B, K := by
      apply Finset.sum_le_sum
      intro h _hh
      apply Finset.sum_le_sum
      intro y _hy
      exact lossFilteredTaggedFiber_bound hY hD hsmall
    _ = (times.card : ℚ) *
        (1 + 3 * D * (2 : ℚ) ^ M / (Y : ℚ)) * (B.card : ℚ) := by
      simp [K]
      ring
end FirstPassageLinearTransport
