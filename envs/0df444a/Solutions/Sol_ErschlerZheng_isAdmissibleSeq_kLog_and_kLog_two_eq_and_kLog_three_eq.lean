-- Prove2me | solution 1 for ErschlerZheng.isAdmissibleSeq_kLog_and_kLog_two_eq_and_kLog_three_eq
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-06T12:44:16.789828+00:00
-- url     : https://prove2.me/submissions/b1300f84-4b94-426f-96a1-a5272d4b2064

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
theorem solution (D A : ℕ) (hD : 2 ≤ D)
    (hA : 0 < A) (hDA : D ∣ A) :
    IsAdmissibleSeq D (kLog A) ∧ kLog A 2 = A ∧ kLog A 3 = A := by
  have hlog2 : Nat.log 2 2 = 1 := Nat.log_eq_of_pow_le_of_lt_pow (by norm_num) (by norm_num)
  have hlog3 : Nat.log 2 3 = 1 := Nat.log_eq_of_pow_le_of_lt_pow (by norm_num) (by norm_num)
  refine ⟨⟨fun m n hmn => Nat.mul_le_mul_left A (Nat.log_mono_right hmn), fun n hn hDn => ?_⟩,
    by simp [kLog, hlog2], by simp [kLog, hlog3]⟩
  have hnD : D ≤ n := Nat.le_of_dvd hn hDn
  have hlog : 0 < Nat.log 2 n := Nat.log_pos (by norm_num) (by omega)
  exact ⟨Nat.mul_pos hA hlog, Dvd.dvd.mul_right hDA _⟩
end
