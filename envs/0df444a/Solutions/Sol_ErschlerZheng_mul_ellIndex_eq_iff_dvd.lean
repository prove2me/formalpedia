-- Prove2me | solution 1 for ErschlerZheng.mul_ellIndex_eq_iff_dvd
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-06T12:44:17.030972+00:00
-- url     : https://prove2.me/submissions/3a929754-be2c-4fc2-9135-b7701ee2dd84

import Mathlib
import Definitions.Def_ErschlerZheng_Grigorchuk
import Definitions.Def_ErschlerZheng_Construction

section
/-!
# Basic facts about sections, `a`, and the generators `b_ω, c_ω, d_ω`

Development helpers for the Grigorchuk part of the Erschler–Zheng mission (not published).
-/

open scoped RightActions
open Garrido

namespace ErschlerZheng

namespace GrigBasic

/-! ### Sections -/

/-! ### The root swap -/

/-! ### `a` and the generators -/

/-! ### Words -/

end GrigBasic

end ErschlerZheng
end

section
/-!
# Fr(D), the four generators, and the index arithmetic of §7.2 (group `frarith`)

Proofs of five small statements backing sentences of the notes:

* `chk_exists_gt_eq_one_and_exists_gt_eq_two_and_tail_ne_and_not_eventually_const_and_exists_ne_of_satisfiesFr`:
  under `SatisfiesFr D ω` the letters `1` and `2` occur after every position, so the tail
  hypotheses of the `evalFree` and `letterGerms` milestones hold and `ω` is not constant;
* `chk_ncard_gens_eq_four_iff_and_card_genSet_eq_four_iff`: `a, b_ω, c_ω, d_ω` are four distinct
  elements exactly when `ω` is not constant;
* `chk_isAdmissibleSeq_kLog_and_kLog_two_eq_and_kLog_three_eq`: `k_n = A⌊log₂ n⌋` is admissible;
* `chk_mul_ellIndex_eq_iff_dvd`: the ℕ division in `ellIndex` is exact iff `D ∣ k`;
* `chk_dvd_sub_add_mod_and_sub_add_mod_lt_two_mul_and_dvd_two_mul_sub_of_isAdmissibleSeq`: the
  exponent of `|𝔉_{j,n}|` is computed exactly in ℕ.
-/

open scoped RightActions
open Garrido

namespace ErschlerZheng

namespace NewFrArith

open GrigBasic

/-! ### Item 1: letters `1` and `2` in every tail -/

/-! ### Item 2: the four generators -/

/-! ### Item 5: the exponent of `|𝔉_{j,n}|` -/

end NewFrArith

open NewFrArith

end ErschlerZheng
end

section
open scoped RightActions
open Garrido
open ErschlerZheng
open NewFrArith
theorem solution (D k j : ℕ) :
    D * ellIndex D k j = j + D - j % D + k ↔ D ∣ k := by
  have h1 : j + D - j % D = D * (j / D) + D := by
    have := Nat.div_add_mod j D
    have := Nat.mod_le j D
    omega
  rw [ellIndex, Nat.mul_div_eq_iff_dvd, h1, Nat.dvd_add_right (dvd_add (dvd_mul_right D _) dvd_rfl)]
end
