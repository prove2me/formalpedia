-- Prove2me | solution 1 for FirstPassageLinearTransport.firstBadLandingEnvelope_card_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:42:36.964785+00:00
-- url     : https://prove2.me/submissions/43291f6f-ad1f-4e52-b154-362978998a78

import Definitions.Def_FirstPassageLinearTransport_AdjustableBarrierDensity
import Definitions.Def_FirstPassageLinearTransport_RankScaledLoss
import Definitions.Def_FirstPassageLinearTransport_FirstBadEnvelope
import Theorems.Thm_FirstPassageLinearTransport_mem_landingBad
import Theorems.Thm_FirstPassageLinearTransport_mem_firstBadLandingEnvelope
import Theorems.Thm_FirstPassageLinearTransport_boolParityCode_eq_word
import Theorems.Thm_FirstPassageLinearTransport_card_biUnion_le_sum
import Theorems.Thm_FirstPassageLinearTransport_lossFiltered_arbitraryTarget_transport_uniform
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
attribute [local simp] FirstPassageLinearTransport.mem_firstBadLandingEnvelope

set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution
    {M L U H : ℕ} {r : ℚ} (t : ℝ)
    (hr : 0 < r) (hUM : U < M)
    (hsmall : ∀ q ∈ Finset.Icc L U,
      ((((q + 2 : ℕ) : ℚ) / r) / ((2 ^ q : ℕ) : ℚ)) ≤ 1 / 3) :
    ((firstBadLandingEnvelope M L U H r t).card : ℚ) ≤
      ∑ q ∈ Finset.Icc L U,
        (H : ℚ) * (1 + 3 * (((q + 2 : ℕ) : ℚ) / r)) *
          (2 : ℚ) ^ M / (2 : ℚ) ^ q * ((landingBad q t).card : ℚ) := by
  classical
  have houter := card_biUnion_le_sum (Finset.Icc L U) fun q =>
    lossFilteredTransportedSources M (2 ^ q) H (landingBad q t)
      (((q + 2 : ℕ) : ℚ) / r)
  have houterQ :
      ((firstBadLandingEnvelope M L U H r t).card : ℚ) ≤
        ∑ q ∈ Finset.Icc L U,
          ((lossFilteredTransportedSources M (2 ^ q) H (landingBad q t)
            (((q + 2 : ℕ) : ℚ) / r)).card : ℚ) := by
    unfold firstBadLandingEnvelope
    exact_mod_cast houter
  calc
    ((firstBadLandingEnvelope M L U H r t).card : ℚ) ≤
        ∑ q ∈ Finset.Icc L U,
          ((lossFilteredTransportedSources M (2 ^ q) H (landingBad q t)
            (((q + 2 : ℕ) : ℚ) / r)).card : ℚ) := houterQ
    _ ≤ ∑ q ∈ Finset.Icc L U,
        (H : ℚ) * (1 + 3 * (((q + 2 : ℕ) : ℚ) / r)) *
          (2 : ℚ) ^ M / (2 : ℚ) ^ q * ((landingBad q t).card : ℚ) := by
      apply Finset.sum_le_sum
      intro q hq
      have hqU : q ≤ U := (Finset.mem_Icc.mp hq).2
      have hqM : q < M := hqU.trans_lt hUM
      have hYM : 2 ^ q < 2 ^ M := Nat.pow_lt_pow_right (by omega) hqM
      have hD : (0 : ℚ) ≤ ((q + 2 : ℕ) : ℚ) / r := by positivity
      have htransport := lossFiltered_arbitraryTarget_transport_uniform
        (M := M) (Y := 2 ^ q) (H := H)
        (D := ((q + 2 : ℕ) : ℚ) / r)
        (landingBad q t) (by positivity) hD (hsmall q hq) hYM
      simpa using htransport
end FirstPassageLinearTransport
