-- Prove2me | solution 1 for GDGen3.rootE_pos
-- status  : ACCEPTED   (prove)
-- author  : @Somehow
-- created : 2026-10-12T06:36:40.750453+00:00
-- url     : https://prove2.me/submissions/6f1902c8-f5d7-4ed0-b493-3ef8b93e91d6

import Mathlib
import Definitions.Def_GDGen3Base
import Definitions.Def_GDGen3RootBase

noncomputable section

open Finset

open GDGen3

namespace GDGen3Proof_rootE_pos

lemma rootE_one (r : ℝ) (hr : 0 < r) : rootE r 1 = (1 + r) * (1 - r) ^ 2 / r := by
  unfold rootE
  norm_num only [pow_one, Nat.cast_one]
  field_simp
  ring

lemma rootE_step (r : ℝ) (hr : 0 < r) (i : ℕ) :
    rootE r (i + 1) - rootE r i = (1 + r) * (1 - r) * (1 / r ^ (i + 1) - 1) := by
  unfold rootE
  push_cast
  rw [pow_succ r i]
  field_simp
  ring

end GDGen3Proof_rootE_pos

open GDGen3Proof_rootE_pos

theorem solution (r : ℝ) (hr : 0 < r) (hr1 : r < 1) (i : ℕ) (hi : 1 ≤ i) : 0 < rootE r i := by
  induction i, hi using Nat.le_induction with
  | base =>
    rw [rootE_one r hr]
    have hd : 0 < 1 - r := by linarith
    positivity
  | succ i hi ih =>
    have hp : 1 < 1 / r ^ (i + 1) := by
      apply (lt_div_iff₀ (pow_pos hr _)).2
      simpa using pow_lt_one₀ (le_of_lt hr) hr1 (by omega : i + 1 ≠ 0)
    have hstep := rootE_step r hr i
    have hg : 0 < (1 + r) * (1 - r) * (1 / r ^ (i + 1) - 1) := by
      have hd : 0 < 1 - r := by linarith
      have hp' : 0 < 1 / r ^ (i + 1) - 1 := by linarith
      positivity
    linarith
