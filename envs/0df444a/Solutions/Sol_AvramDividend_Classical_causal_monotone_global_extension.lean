-- Prove2me | solution 1 for AvramDividend.Classical.causal_monotone_global_extension
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T21:59:37.397177+00:00
-- url     : https://prove2.me/submissions/dbf71a72-76f5-470e-af4a-43229890d261

import Mathlib.Order.Monotone.Basic
import Definitions.Def_AvramDividend_Classical_ScaleFunction
open AvramDividend.Classical Set

theorem solution
    (f : ℝ → ℝ)
    (hzero : ∀ x : ℝ, x < 0 → f x = 0)
    (hnonneg : ∀ x : ℝ, 0 ≤ x → 0 ≤ f x)
    (hmono : MonotoneOn f (Set.Ici (0 : ℝ))) :
    Monotone f := by
  intro a b hab
  rcases lt_or_ge b 0 with hb | hb
  · rw [hzero a (lt_of_le_of_lt hab hb), hzero b hb]
  rcases lt_or_ge a 0 with ha | ha
  · rw [hzero a ha]; exact hnonneg b hb
  · exact hmono (Set.mem_Ici.2 ha) (Set.mem_Ici.2 hb) hab
