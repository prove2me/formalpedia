-- Prove2me | solution 1 for GRH.dirichlet_zero_free_bound_below_record
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-21T19:11:06.057844+00:00
-- url     : https://prove2.me/submissions/6b51c461-40ed-4d74-af6d-9d8914f3e6bd
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_AlpoGe_galoisLocalGlobalStrong_recParameter
import Theorems.Thm_AlpoGe_everyCharacter_of_row

/-!
Reduction (proof-sketch) of `GRH.dirichlet_zero_free_bound_below_record` to the two Open
statements that carry the top-level cut of the alpo.ge release:

* `AlpoGe.galoisLocalGlobalStrong_recParameter` : the proposition `Row0b IsRecT`;
* `AlpoGe.everyCharacter_of_row` : `Row0b IsRecT` implies `L(χ, s) ≠ 0` for `1/2 < Re s`
  away from the pole.

Modus ponens gives non-vanishing on the whole half-plane, in particular on the sub-record
range; the cap `hcap` is not used, and the pole exclusion is converted by De Morgan.
Both inputs are Open and unverified here: this proves nothing about L-functions.
-/

theorem solution
    {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) {s : ℂ}
    (hs : (1 / 2 : ℝ) < s.re)
    (hpole : ¬ (χ = 1 ∧ s = 1))
    (hcap : s.re ≤ 0.8749570698) :
    DirichletCharacter.LFunction χ s ≠ 0 :=
  AlpoGe.everyCharacter_of_row AlpoGe.galoisLocalGlobalStrong_recParameter q χ s hs
    (not_and_or.mp hpole)
