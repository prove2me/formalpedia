-- Prove2me | solution 1 for AvramDividend.Classical.barrierFuture_sSup_sub_const_image
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T21:13:20.343324+00:00
-- url     : https://prove2.me/submissions/17262ae5-d52d-4ef0-9589-a7a40c7562ab

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {α : Type*} (g : α → ℝ) (s : Set α) (c : ℝ)
    (hne : s.Nonempty) (hbound : BddAbove (g '' s)) :
    sSup ((fun x => g x - c) '' s) = sSup (g '' s) - c := by
  have : (fun x => g x - c) '' s = (OrderIso.addRight (-c)) '' (g '' s) := by
    rw [Set.image_image]; simp [sub_eq_add_neg]
  rw [this, ← (OrderIso.addRight (-c)).map_csSup' (hne.image g) hbound]
  simp [sub_eq_add_neg]
