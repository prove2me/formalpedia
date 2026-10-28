-- Prove2me | solution 1 for AvramDividend.Classical.levy_running_infimum_adapted
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-27T16:50:34.610219+00:00
-- url     : https://prove2.me/submissions/149c16da-664b-4b71-8799-15b7e0afa8fb

import Mathlib.Topology.Bases
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Group.Pointwise.Set.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Theorems.Thm_AvramDividend_Classical_countable_pastSup_adapted_of_adapted
import Theorems.Thm_AvramDividend_Classical_dense_timeSup_with_endpoint
import Theorems.Thm_AvramDividend_Classical_levy_path_bddBelow_finite_horizon

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- The actual negative running infimum is measurable in the past filtration
at each deterministic time, including the possibly discontinuous endpoint. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) :
    Adapted 𝓕 (fun t ω =>
      -sInf {y : ℝ | ∃ s : ℝ≥0, s ≤ t ∧ y = X.X s ω}) := by
  obtain ⟨S₀, hcount₀, hdense₀⟩ :=
    TopologicalSpace.exists_countable_dense ℝ≥0
  let S : Set ℝ≥0 := S₀ ∪ {(0 : ℝ≥0)}
  have hcount : S.Countable :=
    hcount₀.union (Set.countable_singleton 0)
  have hdense : Dense S := hdense₀.mono Set.subset_union_left
  have hzero : (0 : ℝ≥0) ∈ S := Or.inr rfl
  have hneg : Adapted 𝓕 (fun t ω => -X.X t ω) := by
    intro t
    exact (X.adapted t).neg
  have hsample : Adapted 𝓕 (fun t ω =>
      ⨆ s : {s : ℝ≥0 // s ∈ S ∧ s ≤ t}, -X.X s.1 ω) :=
    countable_pastSup_adapted_of_adapted
      (fun t ω => -X.X t ω) hneg S hcount
  intro t
  have heq : (fun ω : Ω =>
      -sInf {y : ℝ | ∃ s : ℝ≥0, s ≤ t ∧ y = X.X s ω}) =
      (fun ω : Ω =>
        max (⨆ s : {s : ℝ≥0 // s ∈ S ∧ s ≤ t}, -X.X s.1 ω)
          (-X.X t ω)) := by
    funext ω
    have hset :
        {y : ℝ | ∃ s : ℝ≥0, s ≤ t ∧ y = X.X s ω} =
        Set.range (fun s : Set.Icc (0 : ℝ≥0) t => X.X s.1 ω) := by
      ext y
      constructor
      · rintro ⟨s, hs, rfl⟩
        exact ⟨⟨s, ⟨zero_le, hs⟩⟩, rfl⟩
      · rintro ⟨s, rfl⟩
        exact ⟨s.1, s.2.2, rfl⟩
    have hsup :
        -sInf {y : ℝ | ∃ s : ℝ≥0, s ≤ t ∧ y = X.X s ω} =
        ⨆ s : Set.Icc (0 : ℝ≥0) t, -X.X s.1 ω := by
      calc
        -sInf {y : ℝ | ∃ s : ℝ≥0, s ≤ t ∧ y = X.X s ω} =
          sSup (-{y : ℝ | ∃ s : ℝ≥0, s ≤ t ∧ y = X.X s ω}) :=
            (Real.sSup_neg _).symm
        _ = sSup (-Set.range (fun s : Set.Icc (0 : ℝ≥0) t =>
            X.X s.1 ω)) := by rw [hset]
        _ = sSup (Set.range (fun s : Set.Icc (0 : ℝ≥0) t =>
            -X.X s.1 ω)) := by rw [Set.neg_range]
        _ = ⨆ s : Set.Icc (0 : ℝ≥0) t, -X.X s.1 ω := rfl
    have hright :
        ∀ v : ℝ≥0, ContinuousWithinAt
          (fun z : ℝ≥0 => -X.X z ω) (Ici v) v := by
      intro v
      exact (X.rightCont ω v).neg
    obtain ⟨M, hM⟩ := levy_path_bddBelow_finite_horizon X t ω
    have hb : BddAbove (Set.range
        (fun s : Set.Icc (0 : ℝ≥0) t => -X.X s.1 ω)) := by
      refine ⟨-M, ?_⟩
      rintro y ⟨s, rfl⟩
      exact neg_le_neg (hM ⟨s.1, s.2.2, rfl⟩)
    calc
      -sInf {y : ℝ | ∃ s : ℝ≥0, s ≤ t ∧ y = X.X s ω} =
        ⨆ s : Set.Icc (0 : ℝ≥0) t, -X.X s.1 ω := hsup
      _ = max (⨆ s : {s : ℝ≥0 // s ∈ S ∧ s ≤ t},
          -X.X s.1 ω) (-X.X t ω) :=
            dense_timeSup_with_endpoint
              (fun z => -X.X z ω) hright S hdense hzero t hb
  change Measurable[𝓕 t] (fun ω : Ω =>
    -sInf {y : ℝ | ∃ s : ℝ≥0, s ≤ t ∧ y = X.X s ω})
  rw [heq]
  exact (hsample t).max (X.adapted t).neg
