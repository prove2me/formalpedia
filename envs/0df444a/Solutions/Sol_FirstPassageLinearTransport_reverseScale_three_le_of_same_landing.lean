-- Prove2me | solution 1 for FirstPassageLinearTransport.reverseScale_three_le_of_same_landing
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:07:31.061887+00:00
-- url     : https://prove2.me/submissions/4f7e6aa5-7b93-45b3-98f0-114770a4a411

import Definitions.Def_FirstPassageLinearTransport_Parity
import Definitions.Def_FirstPassageLinearTransport_FirstPassage
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



set_option autoImplicit true
open FirstPassageLinearTransport
namespace FirstPassageLinearTransport
theorem _root_.solution {n₁ n₂ h y : ℕ}
    (hy₁ : orbit h n₁ = y) (hy₂ : orbit h n₂ = y)
    (hs : oddCount n₁ h < oddCount n₂ h) :
    3 * reverseScale n₂ h ≤ reverseScale n₁ h := by
  let N : ℚ := (2 : ℚ) ^ h * (y : ℚ)
  let d₁ : ℚ := (3 : ℚ) ^ (oddCount n₁ h)
  let d₂ : ℚ := (3 : ℚ) ^ (oddCount n₂ h)
  have hd₁ : 0 < d₁ := by
    dsimp [d₁]
    positivity
  have hd₂ : 0 < d₂ := by
    dsimp [d₂]
    positivity
  have hN : 0 ≤ N := by
    dsimp [N]
    positivity
  have hpow : 3 * d₁ ≤ d₂ := by
    dsimp [d₁, d₂]
    have hp :
        (3 : ℚ) ^ (oddCount n₁ h + 1) ≤
          (3 : ℚ) ^ (oddCount n₂ h) :=
      pow_le_pow_right₀ (by norm_num) (by omega)
    simpa [pow_succ, mul_comm] using hp
  have hcross : 3 * N * d₁ ≤ N * d₂ := by
    have := mul_le_mul_of_nonneg_left hpow hN
    simpa [mul_assoc, mul_comm, mul_left_comm] using this
  simp only [reverseScale, hy₁, hy₂]
  change 3 * (N / d₂) ≤ N / d₁
  rw [← mul_div_assoc]
  exact (div_le_div_iff₀ hd₂ hd₁).2 hcross
end FirstPassageLinearTransport
