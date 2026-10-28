-- Prove2me | solution 1 for AvramDividend.Classical.stronglyProgressive_of_past_finiteRange_sample
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T10:46:03.924633+00:00
-- url     : https://prove2.me/submissions/977db66f-c044-47e3-97d0-2169f730a1ff

import Mathlib.Probability.Process.Adapted
import Mathlib.MeasureTheory.Group.Arithmetic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Topology.Instances.ENNReal.Lemmas

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (𝓕 : Filtration ℝ≥0 mΩ) (D : ℝ≥0 → Ω → ℝ)
    (hAdapted : StronglyAdapted 𝓕 D)
    (g : ℝ≥0 → ℝ≥0) (hg_meas : Measurable g)
    (hg_past : ∀ t, g t ≤ t)
    (hg_finite : ∀ T, (g '' Iic T).Finite) :
    IsStronglyProgressive 𝓕 (fun t ω => D (g t) ω) := by
  classical
  apply IsProgressive.isStronglyProgressive
  intro T
  let s : Finset ℝ≥0 := (hg_finite T).toFinset
  have hs_time : ∀ r ∈ s, r ≤ T := by
    intro r hr
    obtain ⟨t, ht, rfl⟩ : r ∈ g '' Iic T :=
      (Set.Finite.mem_toFinset (hg_finite T)).mp hr
    exact (hg_past t).trans ht
  have hg_prod :
      Measurable[Subtype.instMeasurableSpace.prod (𝓕 T)]
        (fun p : Iic T × Ω => g (p.1 : ℝ≥0)) := by
    exact hg_meas.comp (measurable_subtype_coe.comp measurable_fst)
  have hterm : ∀ r ∈ s,
      Measurable[Subtype.instMeasurableSpace.prod (𝓕 T)]
        (fun p : Iic T × Ω =>
          if g (p.1 : ℝ≥0) = r then D r p.2 else 0) := by
    intro r hr
    have hd : Measurable[𝓕 T] (D r) :=
      ((hAdapted r).mono (𝓕.mono (hs_time r hr))).measurable
    have hd_prod :
        Measurable[Subtype.instMeasurableSpace.prod (𝓕 T)]
          (fun p : Iic T × Ω => D r p.2) := by
      exact hd.comp measurable_snd
    have hp :
        MeasurableSet[Subtype.instMeasurableSpace.prod (𝓕 T)]
          {p : Iic T × Ω | g (p.1 : ℝ≥0) = r} := by
      simpa only [Set.preimage, Set.mem_singleton_iff] using
        hg_prod (measurableSet_singleton r)
    exact Measurable.ite hp hd_prod measurable_const
  have hsum :
      Measurable[Subtype.instMeasurableSpace.prod (𝓕 T)]
        (fun p : Iic T × Ω =>
          ∑ r ∈ s, if g (p.1 : ℝ≥0) = r then D r p.2 else 0) :=
    Finset.measurable_fun_sum s hterm
  convert hsum using 1
  ext p
  have hmem : g (p.1 : ℝ≥0) ∈ s :=
    (Set.Finite.mem_toFinset (hg_finite T)).mpr ⟨p.1, p.1.property, rfl⟩
  exact (Finset.sum_ite_eq_of_mem s (g (p.1 : ℝ≥0))
    (fun r => D r p.2) hmem).symm
