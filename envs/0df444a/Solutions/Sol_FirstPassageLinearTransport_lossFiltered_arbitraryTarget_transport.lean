-- Prove2me | solution 1 for FirstPassageLinearTransport.lossFiltered_arbitraryTarget_transport
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:40:58.425249+00:00
-- url     : https://prove2.me/submissions/611c561f-d8d1-4b42-a71b-1e3b595103b1

import Definitions.Def_FirstPassageLinearTransport_Transport
import Definitions.Def_FirstPassageLinearTransport_LossTransport
import Theorems.Thm_FirstPassageLinearTransport_mem_lossFilteredTaggedFiber
import Theorems.Thm_FirstPassageLinearTransport_lossFilteredTaggedFiber_bound
import Theorems.Thm_FirstPassageLinearTransport_mem_lossFilteredTransportedSources
import Theorems.Thm_FirstPassageLinearTransport_card_biUnion_le_sum
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
    (hsmall : D / (Y : ℚ) ≤ 1 / 3) :
    ((lossFilteredTransportedSources M Y H B D).card : ℚ) ≤
      (H : ℚ) * (1 + 3 * D * (2 : ℚ) ^ M / (Y : ℚ)) *
        (B.card : ℚ) := by
  classical
  have houter := card_biUnion_le_sum (Finset.range H)
    (fun t => B.biUnion fun y =>
      lossFilteredTaggedFiber M Y (t + 1) y D)
  have hinner :
      ∀ t ∈ Finset.range H,
        (B.biUnion fun y =>
            lossFilteredTaggedFiber M Y (t + 1) y D).card ≤
          ∑ y ∈ B, (lossFilteredTaggedFiber M Y (t + 1) y D).card := by
    intro t _ht
    exact card_biUnion_le_sum B fun y =>
      lossFilteredTaggedFiber M Y (t + 1) y D
  have hcardNat :
      (lossFilteredTransportedSources M Y H B D).card ≤
        ∑ t ∈ Finset.range H, ∑ y ∈ B,
          (lossFilteredTaggedFiber M Y (t + 1) y D).card := by
    unfold lossFilteredTransportedSources
    calc
      ((Finset.range H).biUnion fun t =>
          B.biUnion fun y =>
            lossFilteredTaggedFiber M Y (t + 1) y D).card ≤
          ∑ t ∈ Finset.range H,
            (B.biUnion fun y =>
              lossFilteredTaggedFiber M Y (t + 1) y D).card := houter
      _ ≤ ∑ t ∈ Finset.range H, ∑ y ∈ B,
          (lossFilteredTaggedFiber M Y (t + 1) y D).card := by
            apply Finset.sum_le_sum
            intro t ht
            exact hinner t ht
  have hcardQ :
      ((lossFilteredTransportedSources M Y H B D).card : ℚ) ≤
        ∑ t ∈ Finset.range H, ∑ y ∈ B,
          ((lossFilteredTaggedFiber M Y (t + 1) y D).card : ℚ) := by
    exact_mod_cast hcardNat
  let K : ℚ := 1 + 3 * D * (2 : ℚ) ^ M / (Y : ℚ)
  calc
    ((lossFilteredTransportedSources M Y H B D).card : ℚ) ≤
        ∑ t ∈ Finset.range H, ∑ y ∈ B,
          ((lossFilteredTaggedFiber M Y (t + 1) y D).card : ℚ) := hcardQ
    _ ≤ ∑ _t ∈ Finset.range H, ∑ _y ∈ B, K := by
      apply Finset.sum_le_sum
      intro t _ht
      apply Finset.sum_le_sum
      intro y _hy
      exact lossFilteredTaggedFiber_bound hY hD hsmall
    _ = (H : ℚ) * (1 + 3 * D * (2 : ℚ) ^ M / (Y : ℚ)) *
        (B.card : ℚ) := by
      simp [K]
      ring
end FirstPassageLinearTransport
