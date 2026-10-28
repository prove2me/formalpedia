-- Prove2me | solution 1 for FunctionalInequalities.Analysis.subgradientImage_sub_inner_add_const_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T13:31:46.568222+00:00
-- url     : https://prove2.me/submissions/0b2cbc29-9f41-4d3b-a646-3b277637dc32

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Convex_Alexandrov

noncomputable section
open MeasureTheory Set
open scoped RealInnerProductSpace ENNReal
section LT11E6SubgradientimageSubAffine
open scoped RealInnerProductSpace
section InnerProduct
variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]
/-- **Subtracting an affine function translates subgradient images** (weak Letwin route, Caffarelli's argument, bookkeeping): `∂(u − ⟪p, ·⟫ − c)(G) = ∂u(G) − p`, hence the volumes agree. -/
theorem solution (u : E → ℝ) (p : E) (c : ℝ) (G : Set E) :
    FunctionalInequalities.Analysis.subgradientImage (fun x => u x - (⟪p, x⟫ + c)) G = (fun q => q - p) '' FunctionalInequalities.Analysis.subgradientImage u G := by
  ext q
  constructor
  · rintro ⟨x, hx, hq⟩
    refine ⟨q + p, ?_, add_sub_cancel_right q p⟩
    refine ⟨x, hx, ?_⟩
    intro y
    have h := hq y
    simp only [inner_sub_right] at h
    simp only [inner_add_left, inner_sub_right]
    linarith
  · rintro ⟨r, ⟨x, hx, hr⟩, rfl⟩
    refine ⟨x, hx, ?_⟩
    intro y
    have h := hr y
    simp only [inner_sub_right] at h
    simp only [inner_sub_left, inner_sub_right]
    linarith
