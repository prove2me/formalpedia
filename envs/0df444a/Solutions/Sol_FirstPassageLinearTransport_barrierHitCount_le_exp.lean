-- Prove2me | solution 1 for FirstPassageLinearTransport.barrierHitCount_le_exp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:24:18.000921+00:00
-- url     : https://prove2.me/submissions/b22417f7-6ce7-4ced-858a-8f66cf47df98

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Data.Fintype.Card
import Mathlib.Logic.Equiv.Fin.Basic
import Definitions.Def_FirstPassageLinearTransport_Parity
import Definitions.Def_FirstPassageLinearTransport_Density
import Definitions.Def_FirstPassageLinearTransport_Barrier
import Theorems.Thm_FirstPassageLinearTransport_barrierHitCount_le_chernoff

set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators
namespace FirstPassageLinearTransport
theorem _root_.solution
    (h : ℝ) (M : ℕ) (hh : 0 ≤ h) (hM : 0 < M) :
    (barrierHitCount (2 * h) M 0 : ℝ) ≤
      (2 : ℝ) ^ (M + 1) * Real.exp (-(2 * h ^ 2 / (M : ℝ))) := by
  have hMreal : 0 < (M : ℝ) := by exact_mod_cast hM
  have hchernoff :=
    barrierHitCount_le_chernoff (2 * h) (2 * h / (M : ℝ)) M
      (by positivity) (by positivity)
  convert hchernoff using 1
  all_goals field_simp
  all_goals ring
end FirstPassageLinearTransport
