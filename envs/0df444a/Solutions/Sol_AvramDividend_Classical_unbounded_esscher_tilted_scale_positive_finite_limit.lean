-- Prove2me | solution 1 for AvramDividend.Classical.unbounded_esscher_tilted_scale_positive_finite_limit
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-21T22:48:14.412716+00:00
-- url     : https://prove2.me/submissions/f3852d86-867f-451b-a246-526f9e903d30
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_scaleFunction_strict_pos_of_unbounded_variation
import Theorems.Thm_AvramDividend_Classical_unbounded_esscher_tilted_scale_monotone_uniform_bound
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set Filter
open scoped NNReal ENNReal Topology

/-!
The elementary bounded-monotone convergence argument is closed here.
The open child isolates the substantive fluctuation-theoretic uniform bound.
-/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hnbv : ¬ X.BoundedVariation)
    (φ : ℝ) (hφ : 0 < φ) (hroot : X.ψ φ = q)
    (V : ℝ → ℝ)
    (hV : ∀ x : ℝ, 0 < x →
      V x = Real.exp (-(φ * x)) * W x) :
    ∃ L : ℝ, 0 < L ∧ Tendsto V atTop (nhds L) := by
  obtain ⟨hVmono, C, hVbound⟩ :=
    unbounded_esscher_tilted_scale_monotone_uniform_bound
      X q hq W hW hnbv φ hφ hroot V hV
  have hWpos : ∀ x : ℝ, 0 < x → 0 < W x :=
    scaleFunction_strict_pos_of_unbounded_variation X q W hW hnbv
  have hVpos : ∀ x : ℝ, 0 < x → 0 < V x := by
    intro x hx
    rw [hV x hx]
    exact mul_pos (Real.exp_pos _) (hWpos x hx)
  let f : ℝ → ℝ := fun x => V (max 1 x)
  have hfmono : Monotone f := by
    intro x y hxy
    apply hVmono
    · exact lt_of_lt_of_le zero_lt_one (le_max_left (1 : ℝ) x)
    · exact lt_of_lt_of_le zero_lt_one (le_max_left (1 : ℝ) y)
    · exact max_le_max_left (1 : ℝ) hxy
  have hfbdd : BddAbove (Set.range f) := by
    refine ⟨C, ?_⟩
    rintro y ⟨x, rfl⟩
    exact hVbound _ (lt_of_lt_of_le zero_lt_one (le_max_left (1 : ℝ) x))
  have hlim := tendsto_atTop_ciSup hfmono hfbdd
  have hfeq : f =ᶠ[atTop] V := by
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
    simp [f, max_eq_right hx]
  have hLpos : 0 < (⨆ x : ℝ, f x) := by
    have hf0 : 0 < f 0 := by
      simpa [f] using hVpos 1 zero_lt_one
    exact lt_of_lt_of_le hf0 (le_ciSup hfbdd (0 : ℝ))
  exact ⟨⨆ x : ℝ, f x, hLpos, hlim.congr' hfeq⟩
