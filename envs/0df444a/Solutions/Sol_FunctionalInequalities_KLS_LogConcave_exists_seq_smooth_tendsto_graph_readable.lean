-- Prove2me | solution 1 for FunctionalInequalities.KLS.LogConcave.exists_seq_smooth_tendsto_graph_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:36:54.715045+00:00
-- url     : https://prove2.me/submissions/78be4fc3-b615-4176-95cd-3d6996dc0907

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_WeightedGradient_Multiplier

noncomputable section
open MeasureTheory Filter Topology
open scoped ContDiff
open FunctionalInequalities.Energy FunctionalInequalities.Energy.WeightedGradient FunctionalInequalities.Analysis.Semigroup
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
section Core
variable {ν : MeasureTheory.ProbabilityMeasure V} (m : MeasureTheory.Measure V) [m.IsAddHaarMeasure] (B : V →L[ℝ] V)
  (hν : FunctionalInequalities.KLS.LogConcave ν) (hi : (interior (ν : MeasureTheory.Measure V).support).Nonempty)
/-- **Smooth compactly supported classes are a graph-norm core of `T̄`.** Every `x ∈ D(T̄)` is the
`L²` limit of classes `[gₙ]` of smooth compactly supported functions whose weighted gradients
`[B ∇gₙ]` converge in `L²` to `T̄ x`. This is the sequential form of
`closure_domRestrict_eq_of_smoothCore_le`; it controls the function and its **first** derivative
only, and says nothing about any second-order quantity. -/
theorem solution (x : (hν.closedWeightedOperator m B hi).domain) :
    ∃ (g : ℕ → V → ℝ) (hg : ∀ n, ContDiff ℝ ∞ (g n)) (hgc : ∀ n, HasCompactSupport (g n)),
      Tendsto (fun n => (FunctionalInequalities.Energy.WeightedGradient.memLp_of_contDiff_hasCompactSupport ν (hg n) (hgc n)).toLp (g n))
          atTop (𝓝 (x : Lp ℝ 2 (ν : Measure V))) ∧
        Tendsto (fun n => (FunctionalInequalities.Energy.WeightedGradient.IsTest.of_contDiff_hasCompactSupport ν B (hg n)
            (hgc n)).memLp_apply.toLp (FunctionalInequalities.Energy.WeightedGradient.apply B (g n))) atTop
          (𝓝 (hν.closedWeightedOperator m B hi x)) := by
  classical
  have hac : (ν : Measure V) ≪ m := hν.absolutelyContinuous_haar m hi
  have hScl : ((hν.weightedOperator m B hi).domRestrict (FunctionalInequalities.Energy.WeightedGradient.smoothCore ν)).closure =
      hν.closedWeightedOperator m B hi :=
    hν.closure_domRestrict_eq_of_smoothCore_le m B hi le_rfl
      (FunctionalInequalities.Energy.WeightedGradient.smoothCore_le_domain_operator ν B hac)
  have hSc : ((hν.weightedOperator m B hi).domRestrict (FunctionalInequalities.Energy.WeightedGradient.smoothCore ν)).IsClosable :=
    (hν.weightedOperator_isClosable m B hi).leIsClosable LinearPMap.domRestrict_le
  have hgraph : ((x : Lp ℝ 2 (ν : Measure V)), hν.closedWeightedOperator m B hi x)
      ∈ ((hν.weightedOperator m B hi).domRestrict (FunctionalInequalities.Energy.WeightedGradient.smoothCore ν)).graph.topologicalClosure := by
    rw [hSc.graph_closure_eq_closure_graph, hScl]
    exact (hν.closedWeightedOperator m B hi).mem_graph x
  obtain ⟨f, hf⟩ :=
    (FunctionalInequalities.Energy.mem_graph_topologicalClosure_iff
      ((hν.weightedOperator m B hi).domRestrict (FunctionalInequalities.Energy.WeightedGradient.smoothCore ν)) _).mp hgraph
  have hmem : ∀ n, ∃ (g : V → ℝ) (hg : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g),
      (f n : Lp ℝ 2 (ν : Measure V))
        = (FunctionalInequalities.Energy.WeightedGradient.memLp_of_contDiff_hasCompactSupport ν hg hgc).toLp g :=
    fun n => (Submodule.mem_inf.mp (f n).2).1
  choose g hg hgc hgeq using hmem
  have hval : ∀ n, (hν.weightedOperator m B hi).domRestrict (FunctionalInequalities.Energy.WeightedGradient.smoothCore ν) (f n) =
      (FunctionalInequalities.Energy.WeightedGradient.IsTest.of_contDiff_hasCompactSupport ν B (hg n) (hgc n)).memLp_apply.toLp
        (FunctionalInequalities.Energy.WeightedGradient.apply B (g n)) := by
    intro n
    have hdom : (f n : Lp ℝ 2 (ν : Measure V)) ∈ (hν.weightedOperator m B hi).domain :=
      (Submodule.mem_inf.mp (f n).2).2
    erw [LinearPMap.domRestrict_apply (x := f n) (y := ⟨_, hdom⟩) rfl]
    exact FunctionalInequalities.Energy.WeightedGradient.operator_apply ν B hac (hν.frontier_support_eq_zero hi)
      (FunctionalInequalities.Energy.WeightedGradient.IsTest.of_contDiff_hasCompactSupport ν B (hg n) (hgc n)) hdom (hgeq n)
  refine ⟨g, hg, hgc, ?_, ?_⟩
  · have h1 : Tendsto (fun n => (f n : Lp ℝ 2 (ν : Measure V))) atTop
        (𝓝 (x : Lp ℝ 2 (ν : Measure V))) := by
      have h := (continuous_fst.tendsto ((x : Lp ℝ 2 (ν : Measure V)),
        hν.closedWeightedOperator m B hi x)).comp hf
      simpa [Function.comp_def] using h
    exact h1.congr fun n => hgeq n
  · have h2 : Tendsto
        (fun n => (hν.weightedOperator m B hi).domRestrict (FunctionalInequalities.Energy.WeightedGradient.smoothCore ν) (f n)) atTop
        (𝓝 (hν.closedWeightedOperator m B hi x)) := by
      have h := (continuous_snd.tendsto ((x : Lp ℝ 2 (ν : Measure V)),
        hν.closedWeightedOperator m B hi x)).comp hf
      simpa [Function.comp_def] using h
    exact h2.congr fun n => hval n
