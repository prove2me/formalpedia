-- Prove2me | solution 1 for BianchiIX.gaussWord_diameter
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T13:11:00.412973+00:00
-- url     : https://prove2.me/submissions/67ad0383-0a91-4a89-ae93-a03e299a0582

import Definitions.Def_BianchiIX_Statistics_GaussInverse
import Theorems.Thm_BianchiIX_gaussWord_lipschitz
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.List.Induction
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open BianchiIX
noncomputable section
open Filter
open scoped Topology


theorem solution (w : List ℕ) (hw : ∀ a ∈ w, 1 ≤ a)
    {x y : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) (hy : y ∈ Set.Icc (0 : ℝ) 1) :
    |gaussWord w x - gaussWord w y| ≤ (1 / 4 : ℝ) ^ (w.length / 2) := by
  have hxy : |x - y| ≤ 1 := abs_le.mpr ⟨by linarith [hx.1, hy.2], by linarith [hy.1, hx.2]⟩
  calc
    _ ≤ (1 / 4 : ℝ) ^ (w.length / 2) * |x - y| := gaussWord_lipschitz w hw hx.1 hy.1
    _ ≤ _ := by simpa using mul_le_mul_of_nonneg_left hxy (by positivity :
      0 ≤ (1 / 4 : ℝ) ^ (w.length / 2))
