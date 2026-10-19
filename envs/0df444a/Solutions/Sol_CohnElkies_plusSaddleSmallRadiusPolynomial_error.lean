-- Prove2me | solution 1 for CohnElkies.plusSaddleSmallRadiusPolynomial_error
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:26.273981+00:00
-- url     : https://prove2.me/submissions/7ddba2e8-b54b-48a7-9808-ff8471623077

import Mathlib
import Definitions.Def_SpherePacking

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped Topology
namespace CohnElkies
theorem _root_.solution
    {ε ℓ : ℝ}
    (hε : 0 < ε) (hℓ : 0 < ℓ)
    (n : ℕ) (hn : 2 * (n : ℝ) ≤ ℓ) :
    |((beta ε - (2 * (n : ℝ) / ℓ) *
          (2 + 2 * (n : ℝ) / ℓ) ^ 2) /
        beta ε) - 1| ≤
      (18 / beta ε) * ((n : ℝ) / ℓ) := by
  have hb : 0 < beta ε := beta_pos hε
  let s : ℝ := 2 * (n : ℝ) / ℓ
  have hs : 0 ≤ s := by
    try dsimp [s]
    positivity
  have hsone : s ≤ 1 := by
    try dsimp [s]
    exact (div_le_iff₀ hℓ).mpr (by simpa using! hn)
  have hsquare : (2 + s) ^ 2 ≤ 9 := by
    nlinarith [mul_nonneg
      (show 0 ≤ 3 - (2 + s) by linarith)
      (show 0 ≤ 3 + (2 + s) by linarith)]
  have hnumerator : 0 ≤ s * (2 + s) ^ 2 :=
    mul_nonneg hs (sq_nonneg _)
  change |(beta ε - s * (2 + s) ^ 2) /
      beta ε - 1| ≤ (18 / beta ε) *
        ((n : ℝ) / ℓ)
  have hid :
      (beta ε - s * (2 + s) ^ 2) / beta ε - 1 =
        -(s * (2 + s) ^ 2) / beta ε := by
    field_simp; ring
  rw [hid, abs_div, abs_neg,
    abs_of_nonneg hnumerator, abs_of_pos hb]
  calc
    s * (2 + s) ^ 2 / beta ε ≤
        s * 9 / beta ε := by
          gcongr
    _ = (18 / beta ε) * ((n : ℝ) / ℓ) := by
      try dsimp [s]
      field_simp; ring
end CohnElkies
