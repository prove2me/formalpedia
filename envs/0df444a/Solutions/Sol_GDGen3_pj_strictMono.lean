-- Prove2me | solution 1 for GDGen3.pj_strictMono
-- status  : ACCEPTED   (prove)
-- author  : @Somehow
-- created : 2026-10-12T06:36:56.421363+00:00
-- url     : https://prove2.me/submissions/ae5e15ca-8612-4384-8488-0a66c741d88a

import Mathlib
import Definitions.Def_GDGen3Base

noncomputable section

open Finset

open GDGen3

namespace GDGen3Proof_pj_strictMono

lemma pj_geometric (r : ℝ) (hr : r ≠ 0) (j : ℕ) :
    pj r j = ((1 / r ^ 2) ^ j - 1) / 2 := by
  unfold pj
  simp only [div_pow, one_pow, ← pow_mul]
  field_simp

end GDGen3Proof_pj_strictMono

open GDGen3Proof_pj_strictMono

theorem solution (r : ℝ) (hr : 0 < r) (hr1 : r < 1) : StrictMono (pj r) := by
  have hz : 1 < 1 / r ^ 2 := by
    apply (lt_div_iff₀ (by positivity : 0 < r ^ 2)).2
    simpa using pow_lt_one₀ (le_of_lt hr) hr1 (by omega : 2 ≠ 0)
  intro a b hab
  rw [pj_geometric r (ne_of_gt hr), pj_geometric r (ne_of_gt hr)]
  exact div_lt_div_of_pos_right (sub_lt_sub_right (pow_lt_pow_right₀ hz hab) 1) (by norm_num)
