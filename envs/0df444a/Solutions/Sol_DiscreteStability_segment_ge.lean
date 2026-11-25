-- Prove2me | solution 1 for DiscreteStability.segment_ge
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T08:57:14.441225+00:00
-- url     : https://prove2.me/submissions/7ad77fbb-4a1a-4fb6-b73c-4a95a6d9e268

import Definitions.Def_DiscreteStability_Basic
import Definitions.Def_DiscreteStability_Ascent
import Theorems.Thm_DiscreteStability_ascent
import Theorems.Thm_DiscreteStability_StepBound_hi_nonneg
import Theorems.Thm_DiscreteStability_StepBound_psd


set_option autoImplicit true
open scoped RealInnerProductSpace
open Set
open DiscreteStability
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {f : E → ℝ} {g : E → E} {S : Set E} {L lo hi : ℝ} {P : E →L[ℝ] E}
namespace DiscreteStability
theorem _root_.solution (hP : StepBound P lo hi) (hL : 0 ≤ L) (hS1 : L * hi ≤ 2) {x : E} {t : ℝ}
    (ht : t ≤ 1)
    (hseg : ∀ τ ∈ Icc (0 : ℝ) t, x + τ • P (g x) ∈ S)
    (hgrad : ∀ z ∈ S, HasFDerivAt f (innerSL ℝ (g z)) z)
    (hlip : ∀ u ∈ S, ∀ v ∈ S, ‖g u - g v‖ ≤ L * ‖u - v‖) :
    ∀ s ∈ Icc (0 : ℝ) t, f x ≤ f (x + s • P (g x)) := by
  intro s hs
  have h := ascent hP hL hseg hgrad hlip s hs
  have hs1 : s ≤ 1 := hs.2.trans ht
  have hcoef : 0 ≤ s * (1 - s / 2 * L * hi) := by
    apply mul_nonneg hs.1
    have : s * (L * hi) ≤ 2 := by nlinarith [mul_nonneg hL (hP.hi_nonneg), hs.1]
    nlinarith
  have := mul_nonneg hcoef (hP.psd (g x))
  linarith
end DiscreteStability
