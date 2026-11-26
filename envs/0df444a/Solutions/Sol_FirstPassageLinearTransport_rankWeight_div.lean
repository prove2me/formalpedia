-- Prove2me | solution 1 for FirstPassageLinearTransport.rankWeight_div
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:42:46.014913+00:00
-- url     : https://prove2.me/submissions/43da272c-91e7-49ac-aa9e-340703513295

import Definitions.Def_FirstPassageLinearTransport_NestedRecertification
import Definitions.Def_FirstPassageLinearTransport_RankScaledLoss
import Theorems.Thm_FirstPassageLinearTransport_rankWeight_nat

set_option autoImplicit true
open FirstPassageLinearTransport
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution (q d : ℕ) :
    ((q + (d + 1) + 2 : ℕ) : ℚ) / (2 : ℚ) ^ (d + 1) ≤
      ((q + 3 : ℕ) : ℚ) / 2 := by
  have hnat := rankWeight_nat q d
  have hq :
      ((q + (d + 1) + 2 : ℕ) : ℚ) ≤
        ((2 ^ d * (q + 3) : ℕ) : ℚ) := by
    exact_mod_cast hnat
  have hden : (0 : ℚ) ≤ (2 : ℚ) ^ (d + 1) := by positivity
  calc
    ((q + (d + 1) + 2 : ℕ) : ℚ) / (2 : ℚ) ^ (d + 1) ≤
        ((2 ^ d * (q + 3) : ℕ) : ℚ) / (2 : ℚ) ^ (d + 1) :=
      div_le_div_of_nonneg_right hq hden
    _ = ((q + 3 : ℕ) : ℚ) / 2 := by
      push_cast
      rw [pow_succ]
      have hp : (2 : ℚ) ^ d ≠ 0 := pow_ne_zero _ (by norm_num)
      field_simp [hp]
end FirstPassageLinearTransport
