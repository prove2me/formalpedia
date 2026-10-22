-- Prove2me | solution 1 for GDGen3.rootPoly_parameter
-- status  : ACCEPTED   (prove)
-- author  : @Somehow
-- created : 2026-10-12T06:24:38.956973+00:00
-- url     : https://prove2.me/submissions/a2e68ad1-7d9c-4833-b73e-f4a24e0e45e1

import Mathlib
import Definitions.Def_GDGen3Base
import Definitions.Def_GDGen3RootBase

noncomputable section

open Finset

open GDGen3

namespace GDGen3Proof_rootPoly_parameter

lemma pj_pos (r : ℝ) (hr : 0 < r) (hr1 : r < 1) (j : ℕ) (hj : j ≠ 0) :
    0 < pj r j := by
  have ht : r ^ (2 * j) < 1 := pow_lt_one₀ (le_of_lt hr) hr1 (by omega)
  exact div_pos (by linarith) (by positivity)

end GDGen3Proof_rootPoly_parameter

open GDGen3Proof_rootPoly_parameter

theorem solution (r : ℝ) (hr : 0 < r) (hr1 : r < 1) (v x : ℝ) (i : ℕ) :
    rootPoly r v i x = rootPoly r (1 + r) i x
      + ((1 + r) - v) * (i + 1) / (1 + r) * ((i : ℝ) / 2 - x) := by
  have hp : pj r (i + 1) ≠ 0 := ne_of_gt (pj_pos r hr hr1 (i + 1) (by omega))
  unfold rootPoly
  field_simp [hp]
  ring
