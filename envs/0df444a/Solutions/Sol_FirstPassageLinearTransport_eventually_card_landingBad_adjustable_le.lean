-- Prove2me | solution 1 for FirstPassageLinearTransport.eventually_card_landingBad_adjustable_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:49:16.416412+00:00
-- url     : https://prove2.me/submissions/13b619da-21ba-4ae3-9068-3906147a381a

import Definitions.Def_FirstPassageLinearTransport_AdjustableBarrierDensity
import Definitions.Def_FirstPassageLinearTransport_RankScaledLoss
import Definitions.Def_FirstPassageLinearTransport_FirstBadEnvelope
import Theorems.Thm_FirstPassageLinearTransport_mem_landingBad
import Theorems.Thm_FirstPassageLinearTransport_card_landingBad_le_shellBad_add_one
import Theorems.Thm_FirstPassageLinearTransport_boolParityCode_eq_word
import Theorems.Thm_FirstPassageLinearTransport_eventually_card_shellInitialWindowBad_adjustable_le
import Theorems.Thm_FirstPassageLinearTransport_mem_dyadicShell
import Theorems.Thm_FirstPassageLinearTransport_mem_lossFilteredTaggedFiber
import Theorems.Thm_FirstPassageLinearTransport_mem_lossFilteredTransportedSources
import Theorems.Thm_FirstPassageLinearTransport_mem_prefixBad
import Theorems.Thm_FirstPassageLinearTransport_mem_taggedFiber
import Theorems.Thm_FirstPassageLinearTransport_mem_transportedSources
import Theorems.Thm_FirstPassageLinearTransport_oddCount_zero
import Theorems.Thm_FirstPassageLinearTransport_orbit_zero
import Theorems.Thm_FirstPassageLinearTransport_parityBit_zero
import Theorems.Thm_FirstPassageLinearTransport_rawOrbit_zero
import Theorems.Thm_FirstPassageLinearTransport_shortcut_zero
attribute [local simp] FirstPassageLinearTransport.boolParityCode_eq_word
attribute [local simp] FirstPassageLinearTransport.mem_dyadicShell
attribute [local simp] FirstPassageLinearTransport.mem_lossFilteredTaggedFiber
attribute [local simp] FirstPassageLinearTransport.mem_lossFilteredTransportedSources
attribute [local simp] FirstPassageLinearTransport.mem_prefixBad
attribute [local simp] FirstPassageLinearTransport.mem_taggedFiber
attribute [local simp] FirstPassageLinearTransport.mem_transportedSources
attribute [local simp] FirstPassageLinearTransport.oddCount_zero
attribute [local simp] FirstPassageLinearTransport.orbit_zero
attribute [local simp] FirstPassageLinearTransport.parityBit_zero
attribute [local simp] FirstPassageLinearTransport.rawOrbit_zero
attribute [local simp] FirstPassageLinearTransport.shortcut_zero


attribute [local simp] FirstPassageLinearTransport.mem_landingBad

set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution
    {lambda t : ℝ} (hlambda0 : 0 ≤ lambda) (hlambda1 : lambda < 1)
    (ht0 : 0 < t) (htA : t < a0) :
    ∀ᶠ q : ℕ in Filter.atTop,
      ((landingBad q t).card : ℝ) ≤
        1 + (2 : ℝ) ^ q *
          Real.exp (-(((q - 1 : ℕ) : ℝ) *
            binaryBarrierRate (adjustableBarrierDisplacement lambda t))) := by
  have htail := eventually_card_shellInitialWindowBad_adjustable_le
    hlambda0 hlambda1 ht0 htA
  rw [Filter.eventually_atTop] at htail ⊢
  obtain ⟨M0, hM0⟩ := htail
  refine ⟨M0 + 1, ?_⟩
  intro q hqM
  have hq1 : 1 ≤ q := by omega
  have hMq : M0 ≤ q - 1 := by omega
  have hshell := hM0 (q - 1) hMq
  have hcardNat := card_landingBad_le_shellBad_add_one hq1 t
  have hcardReal :
      ((landingBad q t).card : ℝ) ≤
        ((shellInitialWindowBad (q - 1) t).card : ℝ) + 1 := by
    exact_mod_cast hcardNat
  calc
    ((landingBad q t).card : ℝ) ≤
        ((shellInitialWindowBad (q - 1) t).card : ℝ) + 1 := hcardReal
    _ ≤ ((2 : ℝ) ^ ((q - 1) + 1) *
          Real.exp (-(((q - 1 : ℕ) : ℝ) *
            binaryBarrierRate (adjustableBarrierDisplacement lambda t)))) + 1 :=
      by simpa [add_comm] using add_le_add_right hshell 1
    _ = 1 + (2 : ℝ) ^ q *
          Real.exp (-(((q - 1 : ℕ) : ℝ) *
            binaryBarrierRate (adjustableBarrierDisplacement lambda t))) := by
      rw [Nat.sub_add_cancel hq1]
      ring
end FirstPassageLinearTransport
