-- Prove2me | solution 1 for FirstPassageLinearTransport.exists_collatzMiddleIntervalMass_le_sqrt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:57:38.711596+00:00
-- url     : https://prove2.me/submissions/a5b1c79a-aa25-4bcf-bba3-4b8ca044c7ae

import Definitions.Def_FirstPassageLinearTransport_SharpEntropyBarrier
import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_FirstPassageLinearTransport_FiniteBallot
import Theorems.Thm_FirstPassageLinearTransport_exists_tiltedBinomialMass_le_sqrt
import Theorems.Thm_FirstPassageLinearTransport_collatzMiddleInterval_support_unique
import Theorems.Thm_FirstPassageLinearTransport_collatzTilt_pos
import Theorems.Thm_FirstPassageLinearTransport_collatzTilt_lt_one
import Theorems.Thm_FirstPassageLinearTransport_collatzTilt_half_lt
import Theorems.Thm_FirstPassageLinearTransport_collatzTilt_lt_two_thirds
import Theorems.Thm_FirstPassageLinearTransport_bernoulliWordWeight_nonneg
import Theorems.Thm_FirstPassageLinearTransport_sum_bernoulliWordWeight_support_eq
import Theorems.Thm_FirstPassageLinearTransport_boolParityCode_eq_word
import Theorems.Thm_FirstPassageLinearTransport_mem_dyadicShell
import Theorems.Thm_FirstPassageLinearTransport_mem_prefixBad
import Theorems.Thm_FirstPassageLinearTransport_oddCount_zero
import Theorems.Thm_FirstPassageLinearTransport_orbit_zero
import Theorems.Thm_FirstPassageLinearTransport_parityBit_zero
import Theorems.Thm_FirstPassageLinearTransport_shortcut_zero
attribute [local simp] FirstPassageLinearTransport.boolParityCode_eq_word
attribute [local simp] FirstPassageLinearTransport.mem_dyadicShell
attribute [local simp] FirstPassageLinearTransport.mem_prefixBad
attribute [local simp] FirstPassageLinearTransport.oddCount_zero
attribute [local simp] FirstPassageLinearTransport.orbit_zero
attribute [local simp] FirstPassageLinearTransport.parityBit_zero
attribute [local simp] FirstPassageLinearTransport.shortcut_zero



set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators Real
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, ∀ a : ℝ, 0 < n →
      ∑ v : Fin n → Bool,
          bernoulliWordWeight collatzTilt v *
            collatzMiddleIntervalIndicator a v ≤
        C / Real.sqrt n := by
  obtain ⟨C, hC, hAtom⟩ :=
    exists_tiltedBinomialMass_le_sqrt
      collatzTilt_half_lt collatzTilt_lt_two_thirds
  refine ⟨C, hC, ?_⟩
  intro n a hn
  classical
  by_cases hex : ∃ v : Fin n → Bool, collatzMiddleInterval a v
  · obtain ⟨v₀, hv₀⟩ := hex
    let k₀ := (boolSupport v₀).card
    calc
      (∑ v : Fin n → Bool,
          bernoulliWordWeight collatzTilt v *
            collatzMiddleIntervalIndicator a v) ≤
          ∑ v : Fin n → Bool,
            bernoulliWordWeight collatzTilt v *
              (if (boolSupport v).card = k₀ then 1 else 0) := by
            apply Finset.sum_le_sum
            intro v _hv
            by_cases hinterval : collatzMiddleInterval a v
            · have hcard : (boolSupport v).card = k₀ := by
                exact collatzMiddleInterval_support_unique hinterval hv₀
              simp [collatzMiddleIntervalIndicator, hinterval, hcard]
            · simp only [collatzMiddleIntervalIndicator, hinterval,
                if_false, mul_zero, zero_le]
              exact mul_nonneg
                (bernoulliWordWeight_nonneg
                  collatzTilt_pos.le collatzTilt_lt_one.le v)
                (by split <;> norm_num)
      _ = tiltedBinomialMass collatzTilt n k₀ :=
        sum_bernoulliWordWeight_support_eq collatzTilt n k₀
      _ ≤ C / Real.sqrt n := hAtom n k₀ hn
  · have hzero :
        (∑ v : Fin n → Bool,
          bernoulliWordWeight collatzTilt v *
            collatzMiddleIntervalIndicator a v) = 0 := by
        apply Finset.sum_eq_zero
        intro v _hv
        have hv : ¬collatzMiddleInterval a v := by
          intro hv
          exact hex ⟨v, hv⟩
        simp [collatzMiddleIntervalIndicator, hv]
    rw [hzero]
    exact div_nonneg hC.le (Real.sqrt_nonneg _)
end FirstPassageLinearTransport
