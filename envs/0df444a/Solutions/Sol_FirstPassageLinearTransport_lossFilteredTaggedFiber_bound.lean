-- Prove2me | solution 1 for FirstPassageLinearTransport.lossFilteredTaggedFiber_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:40:07.628048+00:00
-- url     : https://prove2.me/submissions/8a4cabb7-3494-4337-aeb1-0cd82b9521c1

import Definitions.Def_FirstPassageLinearTransport_Transport
import Definitions.Def_FirstPassageLinearTransport_LossTransport
import Theorems.Thm_FirstPassageLinearTransport_reverseProduct_le_one
import Theorems.Thm_FirstPassageLinearTransport_one_sub_div_le_reverseProduct_of_scaledLoss
import Theorems.Thm_FirstPassageLinearTransport_mem_lossFilteredTaggedFiber
import Theorems.Thm_FirstPassageLinearTransport_lossFiltered_oddCount_rigidity
import Theorems.Thm_FirstPassageLinearTransport_finset_card_le_one_add_span
import Theorems.Thm_FirstPassageLinearTransport_mem_dyadicShell
import Theorems.Thm_FirstPassageLinearTransport_mem_taggedFiber
import Theorems.Thm_FirstPassageLinearTransport_mem_transportedSources
import Theorems.Thm_FirstPassageLinearTransport_oddCount_zero
import Theorems.Thm_FirstPassageLinearTransport_orbit_zero
import Theorems.Thm_FirstPassageLinearTransport_parityBit_zero
import Theorems.Thm_FirstPassageLinearTransport_reverseScale_nonneg
import Theorems.Thm_FirstPassageLinearTransport_reverse_product_identity
import Theorems.Thm_FirstPassageLinearTransport_shortcut_zero
attribute [local simp] FirstPassageLinearTransport.mem_dyadicShell
attribute [local simp] FirstPassageLinearTransport.mem_taggedFiber
attribute [local simp] FirstPassageLinearTransport.mem_transportedSources
attribute [local simp] FirstPassageLinearTransport.oddCount_zero
attribute [local simp] FirstPassageLinearTransport.orbit_zero
attribute [local simp] FirstPassageLinearTransport.parityBit_zero
attribute [local simp] FirstPassageLinearTransport.shortcut_zero


attribute [local simp] FirstPassageLinearTransport.mem_lossFilteredTaggedFiber

set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution
    {M Y h y : ℕ} {D : ℚ}
    (hY : 0 < Y) (hD : 0 ≤ D)
    (hsmall : D / (Y : ℚ) ≤ 1 / 3) :
    ((lossFilteredTaggedFiber M Y h y D).card : ℚ) ≤
      1 + 3 * D * (2 : ℚ) ^ M / (Y : ℚ) := by
  classical
  by_cases hf : (lossFilteredTaggedFiber M Y h y D).Nonempty
  · rcases hf with ⟨n₀, hn₀⟩
    let A : ℚ := reverseScale n₀ h
    let ε : ℚ := D / (Y : ℚ)
    have hmem₀ := mem_lossFilteredTaggedFiber.mp hn₀
    have hn₀pos : 0 < n₀ := by
      have hlo := (mem_dyadicShell.mp hmem₀.1).1
      have hp : 0 < 2 ^ M := by positivity
      omega
    have hA0 : 0 ≤ A := by
      dsimp [A]
      exact reverseScale_nonneg n₀ h
    have hε0 : 0 ≤ ε := by
      dsimp [ε]
      positivity
    have hfactor : (2 / 3 : ℚ) ≤ 1 - ε := by
      dsimp [ε]
      linarith
    have hbounds : ∀ n ∈ lossFilteredTaggedFiber M Y h y D,
        (1 - ε) * A ≤ (n : ℚ) ∧ (n : ℚ) ≤ A := by
      intro n hn
      have hmem := mem_lossFilteredTaggedFiber.mp hn
      have hnpos : 0 < n := by
        have hlo := (mem_dyadicShell.mp hmem.1).1
        have hp : 0 < 2 ^ M := by positivity
        omega
      have hcount := lossFiltered_oddCount_rigidity hn hn₀ hY hD hsmall
      have hscale : reverseScale n h = A := by
        dsimp [A]
        simp only [reverseScale, hmem.2.2.1, hmem₀.2.2.1, hcount]
      have hid : (n : ℚ) = A * reverseProduct n h := by
        rw [← hscale]
        simpa [reverseScale] using reverse_product_identity hnpos h
      have hpLow := one_sub_div_le_reverseProduct_of_scaledLoss
        hnpos hY hmem.2.2.2
      have hpUp := reverseProduct_le_one hnpos h
      dsimp [ε] at hid hpLow ⊢
      constructor
      · rw [hid]
        simpa [mul_comm] using mul_le_mul_of_nonneg_left hpLow hA0
      · rw [hid]
        simpa only [mul_one] using mul_le_mul_of_nonneg_left hpUp hA0
    have hn₀lower := (hbounds n₀ hn₀).1
    have hn₀ltNat := (mem_dyadicShell.mp hmem₀.1).2
    have hn₀lt : (n₀ : ℚ) < (2 : ℚ) ^ (M + 1) := by
      exact_mod_cast hn₀ltNat
    have hAupper : A < (3 / 2 : ℚ) * (2 : ℚ) ^ (M + 1) := by
      have htwoThird : (2 / 3 : ℚ) * A ≤ n₀ :=
        (mul_le_mul_of_nonneg_right hfactor hA0).trans hn₀lower
      nlinarith
    have hspan :
        ((lossFilteredTaggedFiber M Y h y D).max' ⟨n₀, hn₀⟩ : ℚ) -
            ((lossFilteredTaggedFiber M Y h y D).min' ⟨n₀, hn₀⟩ : ℚ) ≤
          3 * D * (2 : ℚ) ^ M / (Y : ℚ) := by
      let s := lossFilteredTaggedFiber M Y h y D
      have hmaxMem : s.max' ⟨n₀, hn₀⟩ ∈ s := Finset.max'_mem _ _
      have hminMem : s.min' ⟨n₀, hn₀⟩ ∈ s := Finset.min'_mem _ _
      have hmax := (hbounds (s.max' ⟨n₀, hn₀⟩) hmaxMem).2
      have hmin := (hbounds (s.min' ⟨n₀, hn₀⟩) hminMem).1
      have hdiff :
          ((s.max' ⟨n₀, hn₀⟩ : ℕ) : ℚ) -
              ((s.min' ⟨n₀, hn₀⟩ : ℕ) : ℚ) ≤ ε * A := by
        nlinarith
      have hmul : ε * A ≤
          ε * ((3 / 2 : ℚ) * (2 : ℚ) ^ (M + 1)) :=
        mul_le_mul_of_nonneg_left hAupper.le hε0
      calc
        ((s.max' ⟨n₀, hn₀⟩ : ℕ) : ℚ) -
              ((s.min' ⟨n₀, hn₀⟩ : ℕ) : ℚ) ≤ ε * A := hdiff
        _ ≤ ε * ((3 / 2 : ℚ) * (2 : ℚ) ^ (M + 1)) := hmul
        _ = 3 * D * (2 : ℚ) ^ M / (Y : ℚ) := by
          dsimp [ε]
          rw [pow_succ]
          ring
    have hcard := finset_card_le_one_add_span
      (lossFilteredTaggedFiber M Y h y D) ⟨n₀, hn₀⟩
    linarith
  · have hempty : lossFilteredTaggedFiber M Y h y D = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp hf
    rw [hempty]
    simp
    positivity
end FirstPassageLinearTransport
