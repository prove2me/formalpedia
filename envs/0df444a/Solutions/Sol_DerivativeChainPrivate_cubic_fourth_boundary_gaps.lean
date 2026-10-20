-- Prove2me | solution 1 for DerivativeChainPrivate.cubic_fourth_boundary_gaps
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-19T11:17:25.805977+00:00
-- url     : https://prove2.me/submissions/053c0f1a-e5bb-4e46-aab9-d4a71d7adb42

import Mathlib
import Definitions.Def_DerivativeChainPrivate_foundations
open Polynomial DerivativeChainPrivate
set_option autoImplicit false



set_option autoImplicit false
open scoped BigOperators

namespace DerivativeChainPrivate













end DerivativeChainPrivate



set_option autoImplicit false
open scoped BigOperators
namespace DerivativeChainPrivate





end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate





end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate



end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate





end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate



end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate







end DerivativeChainPrivate

open DerivativeChainPrivate in
theorem solution :
    let α₆ := (28 - 3 * Real.sqrt 70) / 55
    let α₇ := (7 - 3 * Real.sqrt 3) / 55
    let α₈ := (28 - 3 * Real.sqrt 26) / 550
    let αq : ℝ := 1 / 55
    let b₆ := (35 - 3 * Real.sqrt 70) / 50
    let b₇ := 7 * (3 - Real.sqrt 3) / 60
    let b₈ := (1274 - 99 * Real.sqrt 26) / 6500
    let bq : ℝ := 1 / 10
    let M₈ := (66924 - 7249 * Real.sqrt 26) / 1690000
    0 < αq ∧ αq < α₈ ∧ α₈ < α₇ ∧ α₇ < α₆ ∧
      b₇ - (α₇ / α₆) * b₆ > 27 / 2000 ∧ b₆ - b₇ > 1 / 24 ∧
      b₈ - (α₈ / α₇) * b₇ > 9 / 2000 ∧ b₇ - b₈ > 9 / 400 ∧
      bq - (αq / α₈) * b₈ > 0 ∧ b₈ - bq > 9 / 1000 ∧
      b₇ - 4 * α₇ > 27 / 2000 ∧ 0 < M₈ ∧ M₈ < 9 / 500 := by
  have hs3 := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
  have hs26 := Real.sq_sqrt (show (0 : ℝ) ≤ 26 by norm_num)
  have hs70 := Real.sq_sqrt (show (0 : ℝ) ≤ 70 by norm_num)
  have h3 : 1732 / 1000 < Real.sqrt 3 ∧ Real.sqrt 3 < 1733 / 1000 := by
    constructor <;> nlinarith only [hs3, Real.sqrt_nonneg 3]
  have h26 : 5099 / 1000 < Real.sqrt 26 ∧ Real.sqrt 26 < 51 / 10 := by
    constructor <;> nlinarith only [hs26, Real.sqrt_nonneg 26]
  have h70 : 8366 / 1000 < Real.sqrt 70 ∧ Real.sqrt 70 < 8367 / 1000 := by
    constructor <;> nlinarith only [hs70, Real.sqrt_nonneg 70]
  let α₆ := (28 - 3 * Real.sqrt 70) / 55
  let α₇ := (7 - 3 * Real.sqrt 3) / 55
  let α₈ := (28 - 3 * Real.sqrt 26) / 550
  let b₆ := (35 - 3 * Real.sqrt 70) / 50
  let b₇ := 7 * (3 - Real.sqrt 3) / 60
  let b₈ := (1274 - 99 * Real.sqrt 26) / 6500
  have ha6 : 527 / 10000 < α₆ ∧ α₆ < 528 / 10000 := by dsimp [α₆]; constructor <;> linarith [h70.1,h70.2]
  have ha7 : 327 / 10000 < α₇ ∧ α₇ < 329 / 10000 := by dsimp [α₇]; constructor <;> linarith [h3.1,h3.2]
  have ha8 : 230 / 10000 < α₈ ∧ α₈ < 232 / 10000 := by dsimp [α₈]; constructor <;> linarith [h26.1,h26.2]
  have hb6 : 1979 / 10000 < b₆ ∧ b₆ < 1981 / 10000 := by dsimp [b₆]; constructor <;> linarith [h70.1,h70.2]
  have hb7 : 1478 / 10000 < b₇ ∧ b₇ < 1480 / 10000 := by dsimp [b₇]; constructor <;> linarith [h3.1,h3.2]
  have hb8 : 1183 / 10000 < b₈ ∧ b₈ < 1185 / 10000 := by dsimp [b₈]; constructor <;> linarith [h26.1,h26.2]
  have h67 : α₇ / α₆ ≤ 5 / 8 := by apply (div_le_iff₀ (by linarith : 0 < α₆)).2; linarith
  have h78 : α₈ / α₇ ≤ 3 / 4 := by apply (div_le_iff₀ (by linarith : 0 < α₇)).2; linarith
  have h8q : (1 / 55 : ℝ) / α₈ ≤ 4 / 5 := by apply (div_le_iff₀ (by linarith : 0 < α₈)).2; linarith
  have hv67 := mul_le_mul_of_nonneg_right h67 (show 0 ≤ b₆ by linarith)
  have hv78 := mul_le_mul_of_nonneg_right h78 (show 0 ≤ b₇ by linarith)
  have hv8q := mul_le_mul_of_nonneg_right h8q (show 0 ≤ b₈ by linarith)
  change 0 < (1 / 55 : ℝ) ∧ 1 / 55 < α₈ ∧ α₈ < α₇ ∧ α₇ < α₆ ∧
      b₇ - (α₇ / α₆) * b₆ > 27 / 2000 ∧ b₆ - b₇ > 1 / 24 ∧
      b₈ - (α₈ / α₇) * b₇ > 9 / 2000 ∧ b₇ - b₈ > 9 / 400 ∧
      1 / 10 - ((1 / 55) / α₈) * b₈ > 0 ∧ b₈ - 1 / 10 > 9 / 1000 ∧
      b₇ - 4 * α₇ > 27 / 2000 ∧ _
  refine ⟨by norm_num, by linarith, by linarith, by linarith,
    by linarith, by linarith, by linarith, by linarith, by linarith, by linarith,
    by linarith, ?_, ?_⟩ <;> linarith [h26.1, h26.2]
