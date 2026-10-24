-- Prove2me | solution 1 for FunctionalInequalities.Analysis.subgradientImage_sub_inner_add_const_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T15:11:53.458923+00:00
-- url     : https://prove2.me/submissions/7d050ba2-6835-4751-8e04-6dab5f9294a2

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_AffineMaximum
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_Alexandrov
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_Legendre
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_Subgradient
import Mathlib
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.Convex.Continuous
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Measure
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.Normed.Affine.Convex
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Data.EReal.Operations
import Mathlib.Topology.Instances.EReal.Lemmas
import Mathlib.Topology.Semicontinuity.Basic

noncomputable section
open MeasureTheory Set
open scoped RealInnerProductSpace ENNReal
section LT11E6SubgradientimageSubAffine
open MeasureTheory Set
open scoped RealInnerProductSpace
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities FunctionalInequalities.Analysis
section InnerProduct
variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities.Analysis in
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
