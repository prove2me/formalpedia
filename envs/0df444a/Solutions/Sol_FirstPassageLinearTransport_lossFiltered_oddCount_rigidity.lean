-- Prove2me | solution 1 for FirstPassageLinearTransport.lossFiltered_oddCount_rigidity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:39:20.036745+00:00
-- url     : https://prove2.me/submissions/7ce324ea-939f-4188-91cd-109b1711d22b

import Definitions.Def_FirstPassageLinearTransport_Transport
import Definitions.Def_FirstPassageLinearTransport_LossTransport
import Theorems.Thm_FirstPassageLinearTransport_reverseProduct_le_one
import Theorems.Thm_FirstPassageLinearTransport_one_sub_div_le_reverseProduct_of_scaledLoss
import Theorems.Thm_FirstPassageLinearTransport_mem_lossFilteredTaggedFiber
import Theorems.Thm_FirstPassageLinearTransport_mem_dyadicShell
import Theorems.Thm_FirstPassageLinearTransport_mem_taggedFiber
import Theorems.Thm_FirstPassageLinearTransport_mem_transportedSources
import Theorems.Thm_FirstPassageLinearTransport_oddCount_zero
import Theorems.Thm_FirstPassageLinearTransport_orbit_zero
import Theorems.Thm_FirstPassageLinearTransport_parityBit_zero
import Theorems.Thm_FirstPassageLinearTransport_reverseScale_nonneg
import Theorems.Thm_FirstPassageLinearTransport_reverseScale_three_le_of_same_landing
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
    {M Y h y n₁ n₂ : ℕ} {D : ℚ}
    (hn₁ : n₁ ∈ lossFilteredTaggedFiber M Y h y D)
    (hn₂ : n₂ ∈ lossFilteredTaggedFiber M Y h y D)
    (hY : 0 < Y) (_hD : 0 ≤ D)
    (hsmall : D / (Y : ℚ) ≤ 1 / 3) :
    oddCount n₁ h = oddCount n₂ h := by
  have hmem₁ := mem_lossFilteredTaggedFiber.mp hn₁
  have hmem₂ := mem_lossFilteredTaggedFiber.mp hn₂
  have hn₁pos : 0 < n₁ := by
    have hlo := (mem_dyadicShell.mp hmem₁.1).1
    have hp : 0 < 2 ^ M := by positivity
    omega
  have hn₂pos : 0 < n₂ := by
    have hlo := (mem_dyadicShell.mp hmem₂.1).1
    have hp : 0 < 2 ^ M := by positivity
    omega
  have hP₁low := one_sub_div_le_reverseProduct_of_scaledLoss
    hn₁pos hY hmem₁.2.2.2
  have hP₂low := one_sub_div_le_reverseProduct_of_scaledLoss
    hn₂pos hY hmem₂.2.2.2
  have hP₁up := reverseProduct_le_one hn₁pos h
  have hP₂up := reverseProduct_le_one hn₂pos h
  have hfactor : (2 / 3 : ℚ) ≤ 1 - D / (Y : ℚ) := by linarith
  have hA₁ := reverseScale_nonneg n₁ h
  have hA₂ := reverseScale_nonneg n₂ h
  have hid₁ : (n₁ : ℚ) = reverseScale n₁ h * reverseProduct n₁ h := by
    simpa [reverseScale] using reverse_product_identity hn₁pos h
  have hid₂ : (n₂ : ℚ) = reverseScale n₂ h * reverseProduct n₂ h := by
    simpa [reverseScale] using reverse_product_identity hn₂pos h
  rcases lt_trichotomy (oddCount n₁ h) (oddCount n₂ h) with hs | hs | hs
  · have hscale := reverseScale_three_le_of_same_landing
      hmem₁.2.2.1 hmem₂.2.2.1 hs
    have hn₁lower : (2 / 3 : ℚ) * reverseScale n₁ h ≤ n₁ := by
      rw [hid₁]
      simpa [mul_comm] using
        mul_le_mul_of_nonneg_left (hfactor.trans hP₁low) hA₁
    have hn₂upper : (n₂ : ℚ) ≤ reverseScale n₂ h := by
      rw [hid₂]
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hP₂up hA₂
    have htwiceQ : (2 : ℚ) * n₂ ≤ n₁ := by
      calc
        (2 : ℚ) * n₂ ≤ 2 * reverseScale n₂ h :=
          mul_le_mul_of_nonneg_left hn₂upper (by norm_num)
        _ ≤ (2 / 3 : ℚ) * reverseScale n₁ h := by nlinarith
        _ ≤ n₁ := hn₁lower
    have htwice : 2 * n₂ ≤ n₁ := by exact_mod_cast htwiceQ
    have hn₁lt := (mem_dyadicShell.mp hmem₁.1).2
    have hn₂lo := (mem_dyadicShell.mp hmem₂.1).1
    rw [pow_succ] at hn₁lt
    omega
  · exact hs
  · have hscale := reverseScale_three_le_of_same_landing
      hmem₂.2.2.1 hmem₁.2.2.1 hs
    have hn₂lower : (2 / 3 : ℚ) * reverseScale n₂ h ≤ n₂ := by
      rw [hid₂]
      simpa [mul_comm] using
        mul_le_mul_of_nonneg_left (hfactor.trans hP₂low) hA₂
    have hn₁upper : (n₁ : ℚ) ≤ reverseScale n₁ h := by
      rw [hid₁]
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hP₁up hA₁
    have htwiceQ : (2 : ℚ) * n₁ ≤ n₂ := by
      calc
        (2 : ℚ) * n₁ ≤ 2 * reverseScale n₁ h :=
          mul_le_mul_of_nonneg_left hn₁upper (by norm_num)
        _ ≤ (2 / 3 : ℚ) * reverseScale n₂ h := by nlinarith
        _ ≤ n₂ := hn₂lower
    have htwice : 2 * n₁ ≤ n₂ := by exact_mod_cast htwiceQ
    have hn₂lt := (mem_dyadicShell.mp hmem₂.1).2
    have hn₁lo := (mem_dyadicShell.mp hmem₁.1).1
    rw [pow_succ] at hn₂lt
    omega
end FirstPassageLinearTransport
