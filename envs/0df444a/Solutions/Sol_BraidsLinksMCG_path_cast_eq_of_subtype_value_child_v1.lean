-- Prove2me | solution 1 for BraidsLinksMCG.path_cast_eq_of_subtype_value_child_v1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-23T17:17:08.664947+00:00
-- url     : https://prove2.me/submissions/c674ac97-6234-486c-8f6a-8705848e06d4

import Mathlib
import Theorems.Thm_BraidsLinksMCG_path_cast_eq_of_pointwise_child_v2

theorem solution {X : Type*} [TopologicalSpace X] {P : X → Prop}
    {a b c d : {x : X // P x}} (p : Path a b) (q : Path c d)
    (hc : c = a) (hd : d = b)
    (h : ∀ t, (p t).val = (q t).val) : p.cast hc hd = q := by
  apply BraidsLinksMCG.path_cast_eq_of_pointwise_child_v2
  intro t
  exact Subtype.ext (h t)
