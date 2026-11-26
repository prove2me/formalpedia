-- Prove2me | solution 1 for FirstPassageLinearTransport.twoRegimeClockPotential_step
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:44:37.806825+00:00
-- url     : https://prove2.me/submissions/65963937-06df-4c77-8e3b-6737dd3dab5b

import Definitions.Def_FirstPassageLinearTransport_TwoRegimeRun
import Definitions.Def_FirstPassageLinearTransport_TwoRegimeClock
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
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution
    {rHi rLo : ℝ} {S qPrev m h q : ℕ}
    (hrHi0 : 0 ≤ rHi) (hrHi1 : rHi < 1)
    (hrLo1 : rLo < 1)
    (hmPrev : m ≤ qPrev) (hhm : h ≤ m)
    (hcontract :
      if S ≤ m then (q : ℝ) ≤ rHi * (m : ℝ)
      else (q : ℝ) ≤ rLo * (m : ℝ)) :
    (h : ℝ) + twoRegimeClockPotential rHi rLo S q ≤
      twoRegimeClockPotential rHi rLo S qPrev := by
  have hdHi : 0 < 1 - rHi := sub_pos.mpr hrHi1
  have hdLo : 0 < 1 - rLo := sub_pos.mpr hrLo1
  have hhmR : (h : ℝ) ≤ (m : ℝ) := by exact_mod_cast hhm
  have hmPrevR : (m : ℝ) ≤ (qPrev : ℝ) := by exact_mod_cast hmPrev
  by_cases hqHigh : S ≤ q
  · have hmHigh : S ≤ m := by
      by_contra hmHigh
      have hactive : (q : ℝ) ≤ rLo * (m : ℝ) := by
        simpa [hmHigh] using hcontract
      have hrmul : rLo * (m : ℝ) ≤ (m : ℝ) := by
        nlinarith [show (0 : ℝ) ≤ (m : ℝ) from Nat.cast_nonneg m]
      have hqm : q ≤ m := by exact_mod_cast hactive.trans hrmul
      omega
    have hactive : (q : ℝ) ≤ rHi * (m : ℝ) := by
      simpa [hmHigh] using hcontract
    have hrmul : rHi * (m : ℝ) ≤ (m : ℝ) := by
      nlinarith [show (0 : ℝ) ≤ (m : ℝ) from Nat.cast_nonneg m]
    have hqm : q ≤ m := by exact_mod_cast hactive.trans hrmul
    have hprevHigh : S ≤ qPrev := hqHigh.trans (hqm.trans hmPrev)
    unfold twoRegimeClockPotential
    rw [if_pos hqHigh, if_pos hprevHigh]
    have hlocal : (h : ℝ) + (q : ℝ) / (1 - rHi) ≤
        (m : ℝ) / (1 - rHi) := by
      calc
        (h : ℝ) + (q : ℝ) / (1 - rHi) ≤
            (m : ℝ) + (rHi * (m : ℝ)) / (1 - rHi) :=
          add_le_add hhmR ((div_le_div_iff_of_pos_right hdHi).2 hactive)
        _ = (m : ℝ) / (1 - rHi) := by
          field_simp [hdHi.ne']
          ring
    have hmono : (m : ℝ) / (1 - rHi) ≤
        (qPrev : ℝ) / (1 - rHi) :=
      (div_le_div_iff_of_pos_right hdHi).2 hmPrevR
    linarith
  · have hqLow : q < S := Nat.lt_of_not_ge hqHigh
    by_cases hprevHigh : S ≤ qPrev
    · unfold twoRegimeClockPotential
      rw [if_neg hqHigh, if_pos hprevHigh]
      have htime : (h : ℝ) ≤ (qPrev : ℝ) / (1 - rHi) := by
        have hmq : (m : ℝ) ≤ (qPrev : ℝ) := hmPrevR
        have hqdiv : (qPrev : ℝ) ≤ (qPrev : ℝ) / (1 - rHi) := by
          apply (le_div_iff₀ hdHi).2
          nlinarith [show (0 : ℝ) ≤ (qPrev : ℝ) from Nat.cast_nonneg qPrev]
        exact hhmR.trans (hmq.trans hqdiv)
      have hqS : (q : ℝ) / (1 - rLo) ≤
          (S : ℝ) / (1 - rLo) :=
        (div_le_div_iff_of_pos_right hdLo).2 (by exact_mod_cast hqLow.le)
      linarith
    · have hprevLow : qPrev < S := Nat.lt_of_not_ge hprevHigh
      have hmLow : ¬ S ≤ m := by omega
      have hactive : (q : ℝ) ≤ rLo * (m : ℝ) := by
        simpa [hmLow] using hcontract
      unfold twoRegimeClockPotential
      rw [if_neg hqHigh, if_neg hprevHigh]
      have hlocal : (h : ℝ) + (q : ℝ) / (1 - rLo) ≤
          (m : ℝ) / (1 - rLo) := by
        calc
          (h : ℝ) + (q : ℝ) / (1 - rLo) ≤
              (m : ℝ) + (rLo * (m : ℝ)) / (1 - rLo) :=
            add_le_add hhmR ((div_le_div_iff_of_pos_right hdLo).2 hactive)
          _ = (m : ℝ) / (1 - rLo) := by
            field_simp [hdLo.ne']
            ring
      have hmono : (m : ℝ) / (1 - rLo) ≤
          (qPrev : ℝ) / (1 - rLo) :=
        (div_le_div_iff_of_pos_right hdLo).2 hmPrevR
      exact hlocal.trans hmono
end FirstPassageLinearTransport
