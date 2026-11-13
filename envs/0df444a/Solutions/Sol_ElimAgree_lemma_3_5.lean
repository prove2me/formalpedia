-- Prove2me | solution 1 for ElimAgree.lemma_3_5
-- status  : ACCEPTED   (prove)
-- author  : @ducloc
-- created : 2026-11-12T13:40:56.483475+00:00
-- url     : https://prove2.me/submissions/df7ec531-5a05-4a1c-b1b9-14098ceba1c2

import Mathlib

set_option autoImplicit false

/-- The elimination inequality: after writing `x = √r₁, y = √r₀, u = √c₁, v = √c₀`, the
difference is a sum of two squares. -/
theorem solution (r₀ r₁ c₀ c₁ : ℝ) (hr₀ : 0 ≤ r₀) (hr₁ : 0 ≤ r₁) (hc₀ : 0 ≤ c₀)
    (hc₁ : 0 ≤ c₁) :
    -((r₁ - r₀) * (c₁ - c₀)) ≤
      2 * c₀ * (Real.sqrt r₁ - Real.sqrt r₀) ^ 2 +
        2 * r₀ * (Real.sqrt c₁ - Real.sqrt c₀) ^ 2 := by
  set x := Real.sqrt r₁ with hx
  set y := Real.sqrt r₀ with hy
  set u := Real.sqrt c₁ with hu
  set v := Real.sqrt c₀ with hv
  have hx2 : x ^ 2 = r₁ := by rw [hx]; exact Real.sq_sqrt hr₁
  have hy2 : y ^ 2 = r₀ := by rw [hy]; exact Real.sq_sqrt hr₀
  have hu2 : u ^ 2 = c₁ := by rw [hu]; exact Real.sq_sqrt hc₁
  have hv2 : v ^ 2 = c₀ := by rw [hv]; exact Real.sq_sqrt hc₀
  rw [← hx2, ← hy2, ← hu2, ← hv2]
  have hP : 0 ≤ (x ^ 2 - y ^ 2) * (u ^ 2 - v ^ 2) +
      2 * v ^ 2 * (x - y) ^ 2 + 2 * y ^ 2 * (u - v) ^ 2 := by
    have h1 : 0 ≤ (v * (x - y) + y * (u - v) + (x - y) * (u - v) / 2) ^ 2 :=
      sq_nonneg _
    have h2 : 0 ≤ ((x - y) * (u - v)) ^ 2 := sq_nonneg _
    nlinarith [h1, h2]
  linarith
