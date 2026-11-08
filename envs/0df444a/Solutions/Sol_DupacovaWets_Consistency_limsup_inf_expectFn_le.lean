-- Prove2me | solution 1 for DupacovaWets.Consistency.limsup_inf_expectFn_le
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-07T06:17:41.152255+00:00
-- url     : https://prove2.me/submissions/79a3607e-c2b4-4c62-82a3-38ceacde1593

import Mathlib
import Definitions.Def_DupacovaWets_Consistency_expect
import Definitions.Def_DupacovaWets_Consistency_ExtendedFunctions
import Definitions.Def_DupacovaWets_Consistency_Assumptions
import Theorems.Thm_DupacovaWets_Consistency_epiConverges_inf_argmin
import Theorems.Thm_DupacovaWets_Consistency_expectFn_epiConverges
open MeasureTheory Filter Topology
open DupacovaWets.Consistency

theorem solution {n : ℕ} {Ξ : Type*} [TopologicalSpace Ξ] [PolishSpace Ξ] [MeasurableSpace Ξ] [BorelSpace Ξ]
    (P : Measure Ξ) [IsProbabilityMeasure P]
    {Z : Type*} [mZ : MeasurableSpace Z] (μ : Measure Z) [IsProbabilityMeasure μ]
    (𝔽 : Filtration ℕ mZ) (Pν : ℕ → Z → Measure Ξ)
    (f : EuclideanSpace ℝ (Fin n) → Ξ → EReal) (S : Set (EuclideanSpace ℝ (Fin n)))
    (h34 : Assumption3_4 f S) (h35 : Assumption3_5 f S P μ 𝔽 Pν) :
    ∀ᵐ ζ ∂μ, limsup (fun k => ⨅ x, expectFn (Pν k ζ) f x) atTop ≤ ⨅ x, expectFn P f x := by
  filter_upwards [expectFn_epiConverges P μ 𝔽 Pν f S h34 h35] with ζ h
  exact (epiConverges_inf_argmin _ _ h.1).1
