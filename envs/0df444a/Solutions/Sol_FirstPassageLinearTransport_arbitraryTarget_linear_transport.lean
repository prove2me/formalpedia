-- Prove2me | solution 1 for FirstPassageLinearTransport.arbitraryTarget_linear_transport
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:40:48.633808+00:00
-- url     : https://prove2.me/submissions/d7bcce61-0768-4d29-851c-378118cf8591

import Definitions.Def_FirstPassageLinearTransport_FirstPassage
import Definitions.Def_FirstPassageLinearTransport_Transport
import Theorems.Thm_FirstPassageLinearTransport_taggedFiber_bound_uniform
import Theorems.Thm_FirstPassageLinearTransport_card_biUnion_le_sum
import Theorems.Thm_FirstPassageLinearTransport_mem_transportedSources
import Theorems.Thm_FirstPassageLinearTransport_mem_dyadicShell
import Theorems.Thm_FirstPassageLinearTransport_mem_taggedFiber
import Theorems.Thm_FirstPassageLinearTransport_oddCount_zero
import Theorems.Thm_FirstPassageLinearTransport_orbit_zero
import Theorems.Thm_FirstPassageLinearTransport_parityBit_zero
import Theorems.Thm_FirstPassageLinearTransport_shortcut_zero
attribute [local simp] FirstPassageLinearTransport.mem_dyadicShell
attribute [local simp] FirstPassageLinearTransport.mem_taggedFiber
attribute [local simp] FirstPassageLinearTransport.oddCount_zero
attribute [local simp] FirstPassageLinearTransport.orbit_zero
attribute [local simp] FirstPassageLinearTransport.parityBit_zero
attribute [local simp] FirstPassageLinearTransport.shortcut_zero


attribute [local simp] FirstPassageLinearTransport.mem_transportedSources

set_option autoImplicit true
open FirstPassageLinearTransport
namespace FirstPassageLinearTransport
theorem _root_.solution {M Y H : ℕ} (B : Finset ℕ)
    (hY : 0 < Y) (_hH : 1 ≤ H)
    (hHY : (H : ℚ) / (2 * (Y : ℚ)) ≤ 1 / 3)
    (hYM : Y < 2 ^ M) :
    ((transportedSources M Y H B).card : ℚ) ≤
      (5 / 2 : ℚ) * (H : ℚ) ^ 2 * (2 : ℚ) ^ M /
        (Y : ℚ) * (B.card : ℚ) := by
  classical
  have houter := card_biUnion_le_sum (Finset.range H)
    (fun t => B.biUnion fun y => taggedFiber M Y (t + 1) y)
  have hinner :
      ∀ t ∈ Finset.range H,
        (B.biUnion fun y => taggedFiber M Y (t + 1) y).card ≤
          ∑ y ∈ B, (taggedFiber M Y (t + 1) y).card := by
    intro t _ht
    exact card_biUnion_le_sum B fun y => taggedFiber M Y (t + 1) y
  have hcardNat :
      (transportedSources M Y H B).card ≤
        ∑ t ∈ Finset.range H, ∑ y ∈ B,
          (taggedFiber M Y (t + 1) y).card := by
    unfold transportedSources
    calc
      ((Finset.range H).biUnion fun t =>
          B.biUnion fun y => taggedFiber M Y (t + 1) y).card ≤
          ∑ t ∈ Finset.range H,
            (B.biUnion fun y => taggedFiber M Y (t + 1) y).card := houter
      _ ≤ ∑ t ∈ Finset.range H, ∑ y ∈ B,
          (taggedFiber M Y (t + 1) y).card := by
            apply Finset.sum_le_sum
            intro t ht
            exact hinner t ht
  have hcardQ :
      ((transportedSources M Y H B).card : ℚ) ≤
        ∑ t ∈ Finset.range H, ∑ y ∈ B,
          ((taggedFiber M Y (t + 1) y).card : ℚ) := by
    exact_mod_cast hcardNat
  let K : ℚ := (5 / 2 : ℚ) * (H : ℚ) * (2 : ℚ) ^ M / (Y : ℚ)
  calc
    ((transportedSources M Y H B).card : ℚ) ≤
        ∑ t ∈ Finset.range H, ∑ y ∈ B,
          ((taggedFiber M Y (t + 1) y).card : ℚ) := hcardQ
    _ ≤ ∑ _t ∈ Finset.range H, ∑ _y ∈ B, K := by
      apply Finset.sum_le_sum
      intro t ht
      apply Finset.sum_le_sum
      intro y _hy
      exact taggedFiber_bound_uniform hY (by omega)
        (by simpa using Finset.mem_range.mp ht) hHY hYM
    _ = (5 / 2 : ℚ) * (H : ℚ) ^ 2 * (2 : ℚ) ^ M /
        (Y : ℚ) * (B.card : ℚ) := by
      simp [K]
      ring
end FirstPassageLinearTransport
