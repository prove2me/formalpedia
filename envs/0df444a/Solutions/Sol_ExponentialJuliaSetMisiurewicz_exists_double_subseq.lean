-- Prove2me | solution 1 for ExponentialJuliaSetMisiurewicz.exists_double_subseq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:06:49.539836+00:00
-- url     : https://prove2.me/submissions/30d3ffbd-57ce-4480-9b57-f8f90bddcbf9

import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Data.Nat.Nth
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Definitions.Def_ExpChaotic_HalfPlane
import Definitions.Def_ExpChaotic_RealAxis

set_option autoImplicit true
open Function Filter Set Metric
open scoped Topology NNReal Uniformity
open ExponentialJuliaSetMisiurewicz
noncomputable section
namespace ExponentialJuliaSetMisiurewicz
theorem _root_.solution {X Y : Type*} [MetricSpace X] [MetricSpace Y]
    {s : Set X} {t : Set Y} (hs : IsCompact s) (ht : IsCompact t)
    {a : ℕ → X} {b : ℕ → Y} (ha : ∀ n, a n ∈ s) (hb : ∀ n, b n ∈ t) :
    ∃ x ∈ s, ∃ y ∈ t, ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Filter.Tendsto (a ∘ φ) Filter.atTop (𝓝 x) ∧
      Filter.Tendsto (b ∘ φ) Filter.atTop (𝓝 y) := by
  obtain ⟨x, hxs, φ₁, hφ₁, hlim₁⟩ := hs.tendsto_subseq ha
  obtain ⟨y, hyt, φ₂, hφ₂, hlim₂⟩ := ht.tendsto_subseq (fun n => hb (φ₁ n))
  refine ⟨x, hxs, y, hyt, φ₁ ∘ φ₂, hφ₁.comp hφ₂, ?_, ?_⟩
  · exact hlim₁.comp hφ₂.tendsto_atTop
  · exact hlim₂
end ExponentialJuliaSetMisiurewicz
