-- Prove2me | solution 1 for CachonCoord.DemandUpdate.p67_margin
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T07:05:21.108621+00:00
-- url     : https://prove2.me/submissions/c72b5004-0ebf-4416-95d6-d0aba650e377

import Mathlib
import Definitions.Def_CachonCoord_DemandUpdate_Model

open MeasureTheory ProbabilityTheory


namespace CachonCoord.DemandUpdate

theorem p67_margin_core (M : Model) (lam w1 w2 b : ℝ) (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1)
    (hb : M.p - b = lam * M.p) (hw2 : w2 - b = lam * M.c2)
    (hw1 : w1 - w2 + lam * M.c2 = lam * M.c1) :
    w2 - M.c2 = w1 - (lam * M.c1 + (1 - lam) * M.c2) ∧
    (lam < 1 → w2 - M.c2 < w1 - M.c1) ∧
    (lam = 1 → w2 - M.c2 = w1 - M.c1) := by
  have h := M.c1_lt_c2
  refine ⟨by linarith, fun hl => ?_, fun hl => ?_⟩
  · nlinarith
  · subst hl; linarith

end CachonCoord.DemandUpdate

open CachonCoord.DemandUpdate


theorem solution (M : Model) (lam w1 w2 b : ℝ) (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1)
    (hb : M.p - b = lam * M.p) (hw2 : w2 - b = lam * M.c2)
    (hw1 : w1 - w2 + lam * M.c2 = lam * M.c1) :
    w2 - M.c2 = w1 - (lam * M.c1 + (1 - lam) * M.c2) ∧
    (lam < 1 → w2 - M.c2 < w1 - M.c1) ∧
    (lam = 1 → w2 - M.c2 = w1 - M.c1) := by
  exact p67_margin_core M lam w1 w2 b hlam0 hlam1 hb hw2 hw1
