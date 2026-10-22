-- Prove2me | solution 2 for GDGen3.rootPoly_expanded
-- status  : ACCEPTED   (prove)
-- author  : @Somehow
-- created : 2026-10-12T06:24:38.190159+00:00
-- url     : https://prove2.me/submissions/611be5dd-2ea7-4b9c-a3ca-b633a3040863

import Mathlib
import Definitions.Def_GDGen3Base
import Definitions.Def_GDGen3RootBase

noncomputable section

open Finset

open GDGen3

namespace GDGen3Proof_rootPoly_expanded

lemma pj_pos (r : ℝ) (hr : 0 < r) (hr1 : r < 1) (j : ℕ) (hj : j ≠ 0) :
    0 < pj r j := by
  have ht : r ^ (2 * j) < 1 := pow_lt_one₀ (le_of_lt hr) hr1 (by omega)
  exact div_pos (by linarith) (by positivity)

end GDGen3Proof_rootPoly_expanded

open GDGen3Proof_rootPoly_expanded

theorem solution (r : ℝ) (hr : 0 < r) (hr1 : r < 1) (v x : ℝ) (i : ℕ) :
    rootPoly r v i x = pj r (i + 1) * x * (1 + x - (1 - r) / (1 + r))
      + v * (i + 1) * x / (1 + r) - v * (i : ℝ) * (i + 1) / (2 * (1 + r))
      + (1 - r) * PiS r i / (1 + r) := by
  have hp : pj r (i + 1) ≠ 0 := ne_of_gt (pj_pos r hr hr1 (i + 1) (by omega))
  unfold rootPoly
  field_simp [hp]
  ring
