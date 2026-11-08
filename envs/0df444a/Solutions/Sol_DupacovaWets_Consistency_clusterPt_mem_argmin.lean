-- Prove2me | solution 1 for DupacovaWets.Consistency.clusterPt_mem_argmin
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-07T06:17:41.852675+00:00
-- url     : https://prove2.me/submissions/2ea2152b-6c93-4c6b-8d3a-a70f0fbae466

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
    ∃ Z₀ : Set Z, MeasurableSet Z₀ ∧ μ Z₀ᶜ = 0 ∧ ∀ ζ ∈ Z₀,
      ∀ xs : ℕ → EuclideanSpace ℝ (Fin n), (∀ k, xs k ∈ argminSet (expectFn (Pν k ζ) f)) →
        ∀ xhat : EuclideanSpace ℝ (Fin n), MapClusterPt xhat atTop xs →
          xhat ∈ argminSet (expectFn P f) := by
  have h := expectFn_epiConverges P μ 𝔽 Pν f S h34 h35
  set A : Set Z := {ζ | ¬ (EpiConverges (fun k => expectFn (Pν k ζ) f) (expectFn P f) ∧
      ∀ x, Tendsto (fun k => expectFn (Pν k ζ) f x) atTop (𝓝 (expectFn P f x)))} with hA
  have hA0 : μ A = 0 := by rw [ae_iff] at h; exact h
  refine ⟨(toMeasurable μ A)ᶜ, (measurableSet_toMeasurable μ A).compl, ?_, ?_⟩
  · rw [compl_compl, measure_toMeasurable]; exact hA0
  · intro ζ hζ xs hxs xhat hcl
    have hgood : ζ ∉ A := fun h' => hζ (subset_toMeasurable μ A h')
    simp only [hA, Set.mem_setOf_eq, not_not] at hgood
    obtain ⟨ψ, hψ, hlim⟩ := TopologicalSpace.FirstCountableTopology.tendsto_subseq hcl
    exact ((epiConverges_inf_argmin _ _ hgood.1).2.1 ψ hψ (xs ∘ ψ) xhat
      (fun k => hxs (ψ k)) hlim).1
