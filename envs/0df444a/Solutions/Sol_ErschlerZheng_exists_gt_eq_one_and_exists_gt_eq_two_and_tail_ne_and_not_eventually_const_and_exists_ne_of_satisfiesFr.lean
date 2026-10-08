-- Prove2me | solution 1 for ErschlerZheng.exists_gt_eq_one_and_exists_gt_eq_two_and_tail_ne_and_not_eventually_const_and_exists_ne_of_satisfiesFr
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-06T11:44:25.802058+00:00
-- url     : https://prove2.me/submissions/154a04c3-5984-4ef8-a0ba-1cb5c1890520

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

theorem exists_gt_one_two {D : ℕ} {ω : ℕ → Fin 3} (hω : SatisfiesFr D ω) (n : ℕ) :
    (∃ k, n < k ∧ ω k = 1) ∧ (∃ k, n < k ∧ ω k = 2) := by
  obtain ⟨m, hm, h2, h1, -⟩ := hω (n + 1)
  have hD : 3 ≤ D := by omega
  have hn : n < (n + 1) * D := by nlinarith
  exact ⟨⟨(n + 1) * D + m + 2, by omega, h1⟩, ⟨(n + 1) * D + m, by omega, h2⟩⟩

theorem exists_gt_ne {D : ℕ} {ω : ℕ → Fin 3} (hω : SatisfiesFr D ω) (n : ℕ) (i : Fin 3) :
    ∃ k, n < k ∧ ω k ≠ i := by
  obtain ⟨⟨k1, hk1, e1⟩, ⟨k2, hk2, e2⟩⟩ := exists_gt_one_two hω n
  by_cases hi : i = 1
  · exact ⟨k2, hk2, by rw [e2, hi]; decide⟩
  · exact ⟨k1, hk1, by rw [e1]; exact fun h => hi h.symm⟩

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
theorem solution
    (D : ℕ) (ω : ℕ → Fin 3) (hω : SatisfiesFr D ω) :
    (∀ n, (∃ k, n < k ∧ ω k = 1) ∧ (∃ k, n < k ∧ ω k = 2)) ∧
    (∀ n, ∀ i : Fin 3, i ≠ ω n → ∃ k, n < k ∧ ω k ≠ i) ∧
    (¬ ∃ i : Fin 3, ∀ᶠ k in Filter.atTop, ω k = i) ∧
    ∃ m n, ω m ≠ ω n := by
  refine ⟨exists_gt_one_two hω, fun n i _ => exists_gt_ne hω n i, ?_, ?_⟩
  · rintro ⟨i, hi⟩
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hi
    obtain ⟨k, hk, hne⟩ := exists_gt_ne hω N i
    exact hne (hN k hk.le)
  · obtain ⟨⟨k1, -, e1⟩, ⟨k2, -, e2⟩⟩ := exists_gt_one_two hω 0
    exact ⟨k1, k2, by rw [e1, e2]; decide⟩
end
