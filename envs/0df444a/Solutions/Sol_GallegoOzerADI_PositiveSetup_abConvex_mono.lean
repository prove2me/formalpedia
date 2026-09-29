-- Prove2me | solution 1 for GallegoOzerADI.PositiveSetup.abConvex_mono
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-09-27T23:40:31.303785+00:00
-- url     : https://prove2.me/submissions/a7f4c9b3-7e71-488a-8cbb-bb371ff01cc8

import Mathlib
import Definitions.Def_GallegoOzerADI_PositiveSetup_ABConvex

open GallegoOzerADI.PositiveSetup

theorem solution (a b a' b' : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (haa' : a ≤ a') (hbb' : b ≤ b')
    (g : ℝ → ℝ) (hg : ABConvex a b g) : ABConvex a' b' g := by
  intro x₁ x₂ hx θ hθ0 hθ1
  have h := hg x₁ x₂ hx θ hθ0 hθ1
  have h1 : θ * (a + g x₁) ≤ θ * (a' + g x₁) :=
    mul_le_mul_of_nonneg_left (by linarith) hθ0
  have h2 : (1 - θ) * (b + g x₂) ≤ (1 - θ) * (b' + g x₂) :=
    mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  linarith
