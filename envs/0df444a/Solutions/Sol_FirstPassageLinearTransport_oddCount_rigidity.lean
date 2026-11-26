-- Prove2me | solution 1 for FirstPassageLinearTransport.oddCount_rigidity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:38:43.073472+00:00
-- url     : https://prove2.me/submissions/894c7f78-0044-4d1f-bbac-fc2dcfaae52f

import Definitions.Def_FirstPassageLinearTransport_Parity
import Definitions.Def_FirstPassageLinearTransport_FirstPassage
import Theorems.Thm_FirstPassageLinearTransport_reverseScale_nonneg
import Theorems.Thm_FirstPassageLinearTransport_firstPassage_reverse_bounds
import Theorems.Thm_FirstPassageLinearTransport_reverseScale_three_le_of_same_landing
import Theorems.Thm_FirstPassageLinearTransport_mem_dyadicShell
attribute [local simp] FirstPassageLinearTransport.mem_dyadicShell



set_option autoImplicit true
open FirstPassageLinearTransport
namespace FirstPassageLinearTransport
theorem _root_.solution {M Y h y n₁ n₂ : ℕ}
    (hn₁ : n₁ ∈ dyadicShell M) (hn₂ : n₂ ∈ dyadicShell M)
    (hY : 0 < Y)
    (hsmall : (h : ℚ) / (2 * (Y : ℚ)) ≤ 1 / 3)
    (hfp₁ : IsFirstPassage Y n₁ h) (hy₁ : orbit h n₁ = y)
    (hfp₂ : IsFirstPassage Y n₂ h) (hy₂ : orbit h n₂ = y) :
    oddCount n₁ h = oddCount n₂ h := by
  have hn₁pos : 0 < n₁ := by
    have := (mem_dyadicShell.mp hn₁).1
    have hpowpos : 0 < 2 ^ M := pow_pos (by omega) M
    omega
  have hn₂pos : 0 < n₂ := by
    have := (mem_dyadicShell.mp hn₂).1
    have hpowpos : 0 < 2 ^ M := pow_pos (by omega) M
    omega
  have hb₁ := firstPassage_reverse_bounds hn₁pos hY hfp₁
  have hb₂ := firstPassage_reverse_bounds hn₂pos hY hfp₂
  have hA₁ := reverseScale_nonneg n₁ h
  have hA₂ := reverseScale_nonneg n₂ h
  rcases lt_trichotomy (oddCount n₁ h) (oddCount n₂ h) with hs | hs | hs
  · have hscale := reverseScale_three_le_of_same_landing hy₁ hy₂ hs
    have htwiceQ : (2 : ℚ) * (n₂ : ℚ) ≤ (n₁ : ℚ) := by
      nlinarith
    have htwice : 2 * n₂ ≤ n₁ := by exact_mod_cast htwiceQ
    have hn₁lt : n₁ < 2 ^ (M + 1) := (mem_dyadicShell.mp hn₁).2
    have hn₂lo : 2 ^ M ≤ n₂ := (mem_dyadicShell.mp hn₂).1
    rw [pow_succ] at hn₁lt
    omega
  · exact hs
  · have hscale := reverseScale_three_le_of_same_landing hy₂ hy₁ hs
    have htwiceQ : (2 : ℚ) * (n₁ : ℚ) ≤ (n₂ : ℚ) := by
      nlinarith
    have htwice : 2 * n₁ ≤ n₂ := by exact_mod_cast htwiceQ
    have hn₂lt : n₂ < 2 ^ (M + 1) := (mem_dyadicShell.mp hn₂).2
    have hn₁lo : 2 ^ M ≤ n₁ := (mem_dyadicShell.mp hn₁).1
    rw [pow_succ] at hn₂lt
    omega
end FirstPassageLinearTransport
