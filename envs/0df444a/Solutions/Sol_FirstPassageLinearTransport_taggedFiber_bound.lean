-- Prove2me | solution 1 for FirstPassageLinearTransport.taggedFiber_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:39:19.455582+00:00
-- url     : https://prove2.me/submissions/0c924ee6-fcb0-4f11-be20-505ad2dac0ec

import Definitions.Def_FirstPassageLinearTransport_Parity
import Definitions.Def_FirstPassageLinearTransport_FirstPassage
import Theorems.Thm_FirstPassageLinearTransport_firstPassage_reverse_bounds
import Theorems.Thm_FirstPassageLinearTransport_oddCount_rigidity
import Theorems.Thm_FirstPassageLinearTransport_mem_taggedFiber
import Theorems.Thm_FirstPassageLinearTransport_finset_card_le_one_add_span
import Theorems.Thm_FirstPassageLinearTransport_taggedFiber_algebra
import Theorems.Thm_FirstPassageLinearTransport_mem_dyadicShell
import Theorems.Thm_FirstPassageLinearTransport_oddCount_zero
import Theorems.Thm_FirstPassageLinearTransport_orbit_zero
import Theorems.Thm_FirstPassageLinearTransport_parityBit_zero
import Theorems.Thm_FirstPassageLinearTransport_shortcut_zero
attribute [local simp] FirstPassageLinearTransport.mem_dyadicShell
attribute [local simp] FirstPassageLinearTransport.oddCount_zero
attribute [local simp] FirstPassageLinearTransport.orbit_zero
attribute [local simp] FirstPassageLinearTransport.parityBit_zero
attribute [local simp] FirstPassageLinearTransport.shortcut_zero


attribute [local simp] FirstPassageLinearTransport.mem_taggedFiber

set_option autoImplicit true
open FirstPassageLinearTransport
namespace FirstPassageLinearTransport
theorem _root_.solution {M Y h y : ℕ}
    (hY : 0 < Y)
    (hsmall : (h : ℚ) / (2 * (Y : ℚ)) ≤ 1 / 3) :
    ((taggedFiber M Y h y).card : ℚ) ≤
      1 + 2 * (h : ℚ) * (2 : ℚ) ^ M /
        (2 * (Y : ℚ) - (h : ℚ)) := by
  classical
  by_cases hf : (taggedFiber M Y h y).Nonempty
  · rcases hf with ⟨n₀, hn₀⟩
    let A : ℚ := reverseScale n₀ h
    let ε : ℚ := (h : ℚ) / (2 * (Y : ℚ))
    have htag₀ := mem_taggedFiber.mp hn₀
    have hn₀pos : 0 < n₀ := by
      have hlo := (mem_dyadicShell.mp htag₀.1).1
      have hp : 0 < 2 ^ M := pow_pos (by omega) M
      omega
    have hb₀ := firstPassage_reverse_bounds hn₀pos hY htag₀.2.1
    have hεnonneg : 0 ≤ ε := by
      dsimp [ε]
      positivity
    have hεle : ε ≤ 1 / 3 := hsmall
    have hfactor : 0 < 1 - ε := by linarith
    have hAupper : A < (2 : ℚ) ^ (M + 1) / (1 - ε) := by
      have hn₀ltNat := (mem_dyadicShell.mp htag₀.1).2
      have hn₀lt : (n₀ : ℚ) < (2 : ℚ) ^ (M + 1) := by
        exact_mod_cast hn₀ltNat
      apply (lt_div_iff₀ hfactor).2
      dsimp [A, ε] at hb₀ ⊢
      nlinarith
    have hsameScale :
        ∀ n ∈ taggedFiber M Y h y, reverseScale n h = A := by
      intro n hn
      have htag := mem_taggedFiber.mp hn
      have hs := oddCount_rigidity htag₀.1 htag.1 hY hsmall
        htag₀.2.1 htag₀.2.2 htag.2.1 htag.2.2
      simp only [reverseScale, htag₀.2.2, htag.2.2, hs, A]
    have hbounds :
        ∀ n ∈ taggedFiber M Y h y,
          (1 - ε) * A ≤ (n : ℚ) ∧ (n : ℚ) ≤ A := by
      intro n hn
      have htag := mem_taggedFiber.mp hn
      have hnpos : 0 < n := by
        have hlo := (mem_dyadicShell.mp htag.1).1
        have hp : 0 < 2 ^ M := pow_pos (by omega) M
        omega
      have hb := firstPassage_reverse_bounds hnpos hY htag.2.1
      rw [hsameScale n hn] at hb
      simpa [ε] using hb
    have hmaxmem : (taggedFiber M Y h y).max' ⟨n₀, hn₀⟩ ∈
        taggedFiber M Y h y := Finset.max'_mem _ _
    have hminmem : (taggedFiber M Y h y).min' ⟨n₀, hn₀⟩ ∈
        taggedFiber M Y h y := Finset.min'_mem _ _
    have hspan := finset_card_le_one_add_span
      (taggedFiber M Y h y) ⟨n₀, hn₀⟩
    have hcardA : ((taggedFiber M Y h y).card : ℚ) ≤ 1 + ε * A := by
      have hmax := (hbounds _ hmaxmem).2
      have hmin := (hbounds _ hminmem).1
      nlinarith
    have hmul : ε * A ≤ ε *
        ((2 : ℚ) ^ (M + 1) / (1 - ε)) :=
      mul_le_mul_of_nonneg_left (le_of_lt hAupper) hεnonneg
    calc
      ((taggedFiber M Y h y).card : ℚ) ≤ 1 + ε * A := hcardA
      _ ≤ 1 + ε * ((2 : ℚ) ^ (M + 1) / (1 - ε)) := by linarith
      _ = 1 + 2 * (h : ℚ) * (2 : ℚ) ^ M /
          (2 * (Y : ℚ) - (h : ℚ)) := by
            rw [taggedFiber_algebra hY hsmall]
  · have hempty : taggedFiber M Y h y = ∅ := Finset.not_nonempty_iff_eq_empty.mp hf
    rw [hempty]
    simp
    have hden : (0 : ℚ) < 2 * (Y : ℚ) - (h : ℚ) := by
      have hYQ : (0 : ℚ) < 2 * (Y : ℚ) := by positivity
      have hscaled := (div_le_iff₀ hYQ).mp hsmall
      have : (h : ℚ) ≤ (2 * (Y : ℚ)) / 3 := by
        nlinarith
      nlinarith
    positivity
end FirstPassageLinearTransport
