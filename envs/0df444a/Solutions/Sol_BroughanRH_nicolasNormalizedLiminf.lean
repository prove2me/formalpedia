-- Prove2me | solution 1 for BroughanRH.nicolasNormalizedLiminf
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-11-23T19:17:10.471518+00:00
-- url     : https://prove2.me/submissions/efbdde79-0c6d-4fb5-93a6-f0ace56e45c8
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_BroughanRH_nicolasNormalizedLower
import Mathlib

theorem solution :
    let li (y : ℝ) : ℝ := Real.eulerMascheroniConstant + Real.log |Real.log y| + ∑' k : ℕ, (Real.log y)^(k+1) / (((k+1 : ℕ) : ℝ) * ((k+1).factorial : ℝ))
    let A (x : ℝ) := (li (Chebyshev.theta x) - (Nat.primeCounting ⌊x⌋₊ : ℝ)) * (Real.log x)^2 / Real.sqrt x
    let β : ℝ := 2 + Real.eulerMascheroniConstant - Real.log Real.pi - 2 * Real.log 2
    ((2 - β : ℝ) : EReal) ≤ Filter.liminf (fun x : ℝ => (A x : EReal)) Filter.atTop := by
  intro li A β
  have h := BroughanRH.nicolasNormalizedLower
  refine Filter.le_liminf_of_le (by isBoundedDefault) ?_
  filter_upwards [Filter.eventually_ge_atTop (37 : ℝ)] with x hx
  exact EReal.coe_le_coe_iff.2 (h x hx)
