-- Prove2me | solution 1 for AvramDividend.Classical.generator_harmonic_at_endpoint_of_continuity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-19T07:29:28.920604+00:00
-- url     : https://prove2.me/submissions/caa6fd5d-ece3-4989-bcb9-2d4790e74699

import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Topology.Order.DenselyOrdered
import Mathlib.Order.Interval.Set.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (a : ℝ) (ha : 0 < a)
    (hdom : X.GeneratorIntegrable W a)
    (hcont : ContinuousOn
      (fun z : ℝ => X.generator W z - q * W z) (Ioc 0 a))
    (hinside : ∀ x ∈ Ioo 0 a,
      X.generator W x - q * W x = 0) :
    X.GeneratorIntegrable W a ∧
      X.generator W a - q * W a = 0 := by
  let g : ℝ → ℝ := fun z => X.generator W z - q * W z
  have hg : EqOn g (fun _ : ℝ => (0 : ℝ)) (Ioo 0 a) := by
    intro z hz
    exact hinside z hz
  have hsubset : Ioc (0 : ℝ) a ⊆ closure (Ioo 0 a) := by
    rw [closure_Ioo (ne_of_lt ha)]
    intro z hz
    exact ⟨le_of_lt hz.1, hz.2⟩
  have hto : EqOn g (fun _ : ℝ => (0 : ℝ)) (Ioc 0 a) :=
    hg.of_subset_closure hcont continuousOn_const Ioo_subset_Ioc_self hsubset
  exact ⟨hdom, hto ⟨ha, le_rfl⟩⟩
