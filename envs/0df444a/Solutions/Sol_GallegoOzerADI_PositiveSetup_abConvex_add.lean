-- Prove2me | solution 1 for GallegoOzerADI.PositiveSetup.abConvex_add
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-28T23:09:26.326825+00:00
-- url     : https://prove2.me/submissions/f1c0356b-88d3-4c5b-b75f-533703277b70

import Mathlib
import Definitions.Def_GallegoOzerADI_PositiveSetup_ABConvex

namespace GallegoOzerADI.PositiveSetup

end GallegoOzerADI.PositiveSetup

open GallegoOzerADI.PositiveSetup

theorem solution (a b a' b' : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (ha' : 0 ≤ a') (hb' : 0 ≤ b')
    (f g : ℝ → ℝ) (hf : ABConvex a b f) (hg : ABConvex a' b' g) (α β : ℝ) (hα : 0 < α)
    (hβ : 0 < β) :
    ABConvex (α * a + β * a') (α * b + β * b') (fun x => α * f x + β * g x) := by
  intro x₁ x₂ hx θ hθ0 hθ1
  have h1 := hf x₁ x₂ hx θ hθ0 hθ1
  have h2 := hg x₁ x₂ hx θ hθ0 hθ1
  have e1 := mul_le_mul_of_nonneg_left h1 hα.le
  have e2 := mul_le_mul_of_nonneg_left h2 hβ.le
  simp only
  nlinarith [e1, e2]
