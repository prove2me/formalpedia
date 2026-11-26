-- Prove2me | solution 1 for FirstPassageLinearTransport.maximalParityRegular_of_not_hitsBarrier
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:23:42.851728+00:00
-- url     : https://prove2.me/submissions/3737d30c-0dde-4ee0-9ea2-2c35a4eb1297

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Data.Fintype.Card
import Mathlib.Logic.Equiv.Fin.Basic
import Definitions.Def_FirstPassageLinearTransport_Parity
import Definitions.Def_FirstPassageLinearTransport_Density
import Definitions.Def_FirstPassageLinearTransport_Barrier
import Theorems.Thm_FirstPassageLinearTransport_prefix_position_le_of_not_hitsBarrier

set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators
namespace FirstPassageLinearTransport
theorem _root_.solution {M n : ℕ} {h : ℝ}
    (hgood : ¬hitsBarrierFrom (2 * h) M 0 (boolParityWord M n)) :
    MaximalParityRegular n M h := by
  intro H hHM
  have hp := prefix_position_le_of_not_hitsBarrier hgood H hHM
  have habs :
      |(2 : ℝ) * ((oddCount n H : ℝ) - (H : ℝ) / 2)| ≤ 2 * h := by
    convert hp using 1
    all_goals ring
  rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)] at habs
  nlinarith
end FirstPassageLinearTransport
