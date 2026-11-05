-- Prove2me | solution 1 for FeinbergPOMDP.WStar.theorem_3_7
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T17:55:21.858386+00:00
-- url     : https://prove2.me/submissions/e07da216-5e60-4ccd-a9ad-d83f603509cd
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_FeinbergPOMDP_WStar_Model
import Theorems.Thm_FeinbergPOMDP_WStar_filter_exists
import Theorems.Thm_FeinbergPOMDP_WStar_lemma_5_3
import Theorems.Thm_FeinbergPOMDP_WStar_corollary_5_4
import Theorems.Thm_FeinbergPOMDP_WStar_lemma_5_6
import Theorems.Thm_FeinbergPOMDP_WStar_theorem_3_5

open scoped ENNReal NNReal Topology
open MeasureTheory ProbabilityTheory Filter FeinbergPOMDP.WStar

theorem solution {X Y A : Type*}
    [TopologicalSpace X] [TopologicalSpace.MetrizableSpace X] [SecondCountableTopology X]
    [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace Y] [TopologicalSpace.MetrizableSpace Y] [SecondCountableTopology Y]
    [MeasurableSpace Y] [BorelSpace Y]
    [TopologicalSpace A] [TopologicalSpace.MetrizableSpace A] [SecondCountableTopology A]
    [MeasurableSpace A] [BorelSpace A]
    [StandardBorelSpace X] [Nonempty X]
    (P : Kernel (X × A) X) [IsMarkovKernel P] (Q : Kernel (A × X) Y) [IsMarkovKernel Q]
    (hP : IsWeaklyContinuous (kernelPM P)) (hQ : IsTVContinuous (kernelPM Q)) :
    IsSetwiseContinuous (fun p : ProbabilityMeasure X × A => obsLaw P Q p.1 p.2) ∧
    AssumptionH P Q ∧
    ∀ H : ProbabilityMeasure X → A → Y → ProbabilityMeasure X,
      IsFilter P Q H → BeliefTransitionWeaklyContinuous P Q H := by
  -- Setwise continuity of R′ from its total-variation continuity (Corollary 5.4).
  have hTV := corollary_5_4 P Q hP hQ
  have hSW : IsSetwiseContinuous (fun p : ProbabilityMeasure X × A => obsLaw P Q p.1 p.2) := by
    intro s ss hss C hC
    have h := hTV s ss hss
    have hreal : Tendsto (fun n => ((obsLaw P Q (ss n).1 (ss n).2 : Measure Y)).real C) atTop
        (𝓝 (((obsLaw P Q s.1 s.2 : Measure Y)).real C)) := by
      rw [Metric.tendsto_atTop]
      intro ε hε
      obtain ⟨N, hN⟩ := h (ε / 2) (half_pos hε)
      refine ⟨N, fun n hn => ?_⟩
      have := hN n hn (C.indicator (1 : Y → ℝ)) (measurable_one.indicator hC)
        (fun t => by
          by_cases ht : t ∈ C <;> simp [Set.indicator, ht])
      simp only at this
      rw [integral_indicator_one hC, integral_indicator_one hC] at this
      rw [Real.dist_eq]
      linarith
    exact (ENNReal.tendsto_toReal_iff (fun n => measure_ne_top _ _) (measure_ne_top _ _)).1 hreal
  -- Assumption (H) from Lemmas 5.3 and 5.6 with a countable base of 𝕏.
  have hH : AssumptionH P Q := by
    obtain ⟨b, hbc, -, hb⟩ := TopologicalSpace.exists_countable_basis X
    have hbne : b.Nonempty := by
      obtain ⟨x⟩ := ‹Nonempty X›
      obtain ⟨U, hU, hxU, -⟩ := hb.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
      exact ⟨U, hU⟩
    obtain ⟨O, rfl⟩ := hbc.exists_eq_range hbne
    obtain ⟨H₀, hH₀⟩ := filter_exists (Y := Y) P Q
    refine (lemma_5_6 P Q O hb ?_ H₀ hH₀).2
    intro s _
    have hopen : IsOpen (⋂ j ∈ s, O j) :=
      isOpen_biInter_finset fun j _ => hb.isOpen ⟨j, rfl⟩
    have := (lemma_5_3 P Q hP hQ (⋂ j ∈ s, O j) ∅ hopen isOpen_empty).2
    simpa using this
  exact ⟨hSW, hH, fun H hHf => theorem_3_5 P Q (Or.inl ⟨hSW, hH⟩) H hHf⟩
