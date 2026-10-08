-- Prove2me | solution 1 for ErschlerZheng.dvd_sub_add_mod_and_sub_add_mod_lt_two_mul_and_dvd_two_mul_sub_of_isAdmissibleSeq
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-06T12:44:17.332212+00:00
-- url     : https://prove2.me/submissions/0c94c35b-0a62-4a31-b78c-3b5d6ab9c360

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

theorem exponent_facts (D : ℕ) (k : ℕ → ℕ) (hk : IsAdmissibleSeq D k) (n : ℕ) (hn : D ∣ n)
    (hn1 : 1 ≤ n) (j : ℕ) (hjn : n < j + k n) (hjn' : j ≤ n) :
    D ∣ n - j + j % D ∧ n - j + j % D < 2 * k n ∧ D ∣ 2 * k n - (n - j + j % D) := by
  have hD : 0 < D := by
    rcases Nat.eq_zero_or_pos D with h | h
    · subst h
      rw [zero_dvd_iff] at hn
      omega
    · exact h
  obtain ⟨hkpos, hkD⟩ := hk.2 n hn1 hn
  have hDk : D ≤ k n := Nat.le_of_dvd hkpos hkD
  have hmod : j % D < D := Nat.mod_lt j hD
  obtain ⟨q, rfl⟩ := hn
  have hj := Nat.div_add_mod j D
  have h1 : D * q - j + j % D = D * q - D * (j / D) := by omega
  have hdvd : D ∣ D * q - j + j % D := by
    rw [h1]
    exact Nat.dvd_sub (dvd_mul_right D q) (dvd_mul_right D (j / D))
  refine ⟨hdvd, by omega, ?_⟩
  exact Nat.dvd_sub (Dvd.dvd.mul_left hkD 2) hdvd

end NewFrArith

open NewFrArith

end ErschlerZheng
end

section
open scoped RightActions
open Garrido
open ErschlerZheng
open NewFrArith
theorem solution
    (D : ℕ) (k : ℕ → ℕ) (hk : IsAdmissibleSeq D k) (n : ℕ) (hn : D ∣ n) (hn1 : 1 ≤ n) (j : ℕ)
    (hjn : n < j + k n) (hjn' : j ≤ n) :
    D ∣ n - j + j % D ∧ n - j + j % D < 2 * k n ∧ D ∣ 2 * k n - (n - j + j % D) :=
  exponent_facts D k hk n hn hn1 j hjn hjn'
end
