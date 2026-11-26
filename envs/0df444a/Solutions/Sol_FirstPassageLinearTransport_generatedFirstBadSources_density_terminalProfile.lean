-- Prove2me | solution 1 for FirstPassageLinearTransport.generatedFirstBadSources_density_terminalProfile
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:00:14.429249+00:00
-- url     : https://prove2.me/submissions/ababb075-246b-4639-a04c-2d4977a4b341

import Definitions.Def_FirstPassageLinearTransport_TerminalTail
import Definitions.Def_FirstPassageLinearTransport_TerminalProfile
import Theorems.Thm_FirstPassageLinearTransport_generatedFirstBadSources_card_real_le
import Theorems.Thm_FirstPassageLinearTransport_rank_transport_multiplier_le
import Theorems.Thm_FirstPassageLinearTransport_landingBad_density_le
import Theorems.Thm_FirstPassageLinearTransport_terminal_rank_sum_le
import Theorems.Thm_FirstPassageLinearTransport_boolParityCode_eq_word
import Theorems.Thm_FirstPassageLinearTransport_mem_dyadicShell
import Theorems.Thm_FirstPassageLinearTransport_mem_firstBadLandingEnvelope
import Theorems.Thm_FirstPassageLinearTransport_mem_generatedFirstBadSources
import Theorems.Thm_FirstPassageLinearTransport_mem_landingBad
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
attribute [local simp] FirstPassageLinearTransport.mem_firstBadLandingEnvelope
attribute [local simp] FirstPassageLinearTransport.mem_generatedFirstBadSources
attribute [local simp] FirstPassageLinearTransport.mem_landingBad
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



set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution
    {M L U H : ℕ} {r : ℚ} {t b b' c' : ℝ}
    (hr : 0 < r) (hUM : U < M) (hL1 : 1 ≤ L)
    (hsmall : ∀ q ∈ Finset.Icc L U,
      ((((q + 2 : ℕ) : ℚ) / r) / ((2 ^ q : ℕ) : ℚ)) ≤ 1 / 3)
    (hlanding : ∀ q ∈ Finset.Icc L U,
      ((landingBad q t).card : ℝ) ≤
        1 + (2 : ℝ) ^ q *
          Real.exp (-(((q - 1 : ℕ) : ℝ) * b)))
    (hb' : 0 < b') (hbb' : b' < b)
    (hc' : 0 < c') (hc2 : c' < Real.log 2) :
    ((generatedFirstBadSources M L U H r t).card : ℝ) /
        (2 : ℝ) ^ M ≤
      (H : ℝ) * (1 + 6 / (r : ℝ)) *
        terminalTailBound b b' c' L := by
  have hrR : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr
  have hcard := generatedFirstBadSources_card_real_le (H := H) t hr hUM hsmall
  let C : ℝ := 1 + 6 / (r : ℝ)
  let profile : ℕ → ℝ := fun q =>
    ((q + 1 : ℕ) : ℝ) *
      (Real.exp (-(Real.log 2 * (q : ℝ))) +
        Real.exp b * Real.exp (-(b * (q : ℝ))))
  have hC0 : 0 ≤ C := by
    dsimp [C]
    positivity
  have hpowM : 0 < (2 : ℝ) ^ M := by positivity
  have hsummand : ∀ q ∈ Finset.Icc L U,
      (H : ℝ) * (1 + 3 * (((q + 2 : ℕ) : ℝ) / (r : ℝ))) *
          (2 : ℝ) ^ M / (2 : ℝ) ^ q *
            ((landingBad q t).card : ℝ) ≤
        (2 : ℝ) ^ M * ((H : ℝ) * C * profile q) := by
    intro q hq
    have hq1 : 1 ≤ q := hL1.trans (Finset.mem_Icc.mp hq).1
    have hmult := rank_transport_multiplier_le hrR q
    have hdensity := landingBad_density_le hq1 (hlanding q hq)
    have hHpow : 0 ≤ (H : ℝ) * (2 : ℝ) ^ M := by positivity
    have htargetDensity :
        0 ≤ ((landingBad q t).card : ℝ) / (2 : ℝ) ^ q := by
      positivity
    have hprofileBase :
        0 ≤ Real.exp (-(Real.log 2 * (q : ℝ))) +
          Real.exp b * Real.exp (-(b * (q : ℝ))) := by positivity
    calc
      (H : ℝ) * (1 + 3 * (((q + 2 : ℕ) : ℝ) / (r : ℝ))) *
          (2 : ℝ) ^ M / (2 : ℝ) ^ q *
            ((landingBad q t).card : ℝ) =
          ((H : ℝ) * (2 : ℝ) ^ M) *
            (1 + 3 * (((q + 2 : ℕ) : ℝ) / (r : ℝ))) *
            (((landingBad q t).card : ℝ) / (2 : ℝ) ^ q) := by ring
      _ ≤ ((H : ℝ) * (2 : ℝ) ^ M) *
          (C * ((q + 1 : ℕ) : ℝ)) *
            (((landingBad q t).card : ℝ) / (2 : ℝ) ^ q) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hmult hHpow) htargetDensity
      _ ≤ ((H : ℝ) * (2 : ℝ) ^ M) *
          (C * ((q + 1 : ℕ) : ℝ)) *
            (Real.exp (-(Real.log 2 * (q : ℝ))) +
              Real.exp b * Real.exp (-(b * (q : ℝ)))) := by
        exact mul_le_mul_of_nonneg_left hdensity (by positivity)
      _ = (2 : ℝ) ^ M * ((H : ℝ) * C * profile q) := by
        dsimp [profile]
        ring
  have hsum :
      ((generatedFirstBadSources M L U H r t).card : ℝ) ≤
        (2 : ℝ) ^ M *
          ((H : ℝ) * C * ∑ q ∈ Finset.Icc L U, profile q) := by
    calc
      ((generatedFirstBadSources M L U H r t).card : ℝ) ≤
          ∑ q ∈ Finset.Icc L U,
            (H : ℝ) *
              (1 + 3 * (((q + 2 : ℕ) : ℝ) / (r : ℝ))) *
              (2 : ℝ) ^ M / (2 : ℝ) ^ q *
                ((landingBad q t).card : ℝ) := hcard
      _ ≤ ∑ q ∈ Finset.Icc L U,
          (2 : ℝ) ^ M * ((H : ℝ) * C * profile q) := by
        exact Finset.sum_le_sum hsummand
      _ = (2 : ℝ) ^ M *
          ((H : ℝ) * C * ∑ q ∈ Finset.Icc L U, profile q) := by
        rw [Finset.mul_sum, Finset.mul_sum]
  have hnormalized :
      ((generatedFirstBadSources M L U H r t).card : ℝ) /
          (2 : ℝ) ^ M ≤
        (H : ℝ) * C * ∑ q ∈ Finset.Icc L U, profile q := by
    apply (div_le_iff₀ hpowM).2
    simpa [mul_assoc, mul_left_comm, mul_comm] using hsum
  have htail := terminal_rank_sum_le hb' hbb' hc' hc2 L U
  have htailProfile :
      ∑ q ∈ Finset.Icc L U, profile q ≤
        weightedTailConstant (Real.log 2) c' *
            Real.exp (-(c' * (L : ℝ))) +
          Real.exp b * weightedTailConstant b b' *
            Real.exp (-(b' * (L : ℝ))) := by
    simpa [profile] using htail
  have hfinal := hnormalized.trans
    (mul_le_mul_of_nonneg_left htailProfile (mul_nonneg (Nat.cast_nonneg H) hC0))
  simpa [terminalTailBound] using hfinal
end FirstPassageLinearTransport
