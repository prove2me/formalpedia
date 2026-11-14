-- Prove2me | solution 1 for BosonicLearn.measure_of_uniform_limit
-- status  : ACCEPTED   (prove)
-- author  : @Senrui Chen
-- created : 2026-11-13T06:03:01.869487+00:00
-- url     : https://prove2.me/submissions/41707c42-06b3-43d0-967d-b37ae2bf5676

import Mathlib

open MeasureTheory Filter Topology
open scoped ENNReal

noncomputable section

theorem solution {X : Type} [MeasurableSpace X] (β : Set X → ℝ) (lam : ℕ → Measure X)
    (hfin : ∀ n, IsFiniteMeasure (lam n)) (ε : ℕ → ℝ) (hε : Tendsto ε atTop (𝓝 0))
    (h : ∀ n C, MeasurableSet C → |β C - (lam n C).toReal| ≤ ε n) :
    ∃ μ : Measure X, IsFiniteMeasure μ ∧ ∀ C, MeasurableSet C → μ C = ENNReal.ofReal (β C) := by
  -- on every measurable set, `λₙ(C) → β(C)`
  have hconv : ∀ C, MeasurableSet C → Tendsto (fun n => (lam n C).toReal) atTop (𝓝 (β C)) := by
    intro C hC
    rw [tendsto_iff_dist_tendsto_zero]
    refine squeeze_zero (fun n => dist_nonneg) (fun n => ?_) hε
    rw [Real.dist_eq, abs_sub_comm]
    exact h n C hC
  have h0 : ∀ C, MeasurableSet C → 0 ≤ β C := fun C hC =>
    ge_of_tendsto (hconv C hC) (Eventually.of_forall fun n => ENNReal.toReal_nonneg)
  -- `β` is finitely additive, hence monotone
  have hadd : ∀ C D, MeasurableSet C → MeasurableSet D → Disjoint C D → β (C ∪ D) = β C + β D := by
    intro C D hC hD hCD
    refine tendsto_nhds_unique (hconv _ (hC.union hD)) (((hconv C hC).add (hconv D hD)).congr fun n => ?_)
    have := hfin n
    rw [measure_union hCD hD, ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)]
  have hempty : β ∅ = 0 := by
    have h1 := hadd ∅ ∅ MeasurableSet.empty MeasurableSet.empty disjoint_bot_left
    simp only [Set.union_self] at h1
    linarith
  have hmono : ∀ C D, MeasurableSet C → MeasurableSet D → C ⊆ D → β C ≤ β D := by
    intro C D hC hD hCD
    have h1 := hadd C (D \ C) hC (hD.diff hC) disjoint_sdiff_self_right
    rw [Set.union_sdiff_cancel hCD] at h1
    linarith [h0 _ (hD.diff hC)]
  -- countable additivity
  have hsig : ∀ ⦃f : ℕ → Set X⦄ (hf : ∀ i, MeasurableSet (f i)),
      Pairwise (Function.onFun Disjoint f) →
      ENNReal.ofReal (β (⋃ i, f i)) = ∑' i, ENNReal.ofReal (β (f i)) := by
    intro f hf hdisj
    have hacc : ∀ K, MeasurableSet (Set.accumulate f K) := fun K => by
      rw [Set.accumulate_def]
      exact MeasurableSet.iUnion fun y => MeasurableSet.iUnion fun _ => hf y
    have hpart : ∀ K, ∑ i ∈ Finset.range (K + 1), ENNReal.ofReal (β (f i)) =
        ENNReal.ofReal (β (Set.accumulate f K)) := by
      intro K
      induction K with
      | zero => simp [Set.accumulate_def]
      | succ K ih =>
        have hd : Disjoint (Set.accumulate f K) (f (K + 1)) := by
          rw [Set.disjoint_left]
          intro x hx hx'
          obtain ⟨y, hy, hxy⟩ := Set.mem_accumulate.mp hx
          exact Set.disjoint_left.mp (hdisj (by omega : y ≠ K + 1)) hxy hx'
        rw [Finset.sum_range_succ, ih, Set.accumulate_succ, hadd _ _ (hacc K) (hf _) hd,
          ENNReal.ofReal_add (h0 _ (hacc K)) (h0 _ (hf _))]
    have hmonoK : Monotone fun K => ENNReal.ofReal (β (Set.accumulate f K)) := fun K K' hK =>
      ENNReal.ofReal_le_ofReal (hmono _ _ (hacc K) (hacc K') (Set.monotone_accumulate hK))
    have hU : MeasurableSet (⋃ i, f i) := MeasurableSet.iUnion hf
    have htend : Tendsto (fun K => β (Set.accumulate f K)) atTop (𝓝 (β (⋃ i, f i))) := by
      rw [Metric.tendsto_atTop]
      intro δ hδ
      obtain ⟨n, hn⟩ := ((tendsto_order.1 hε).2 (δ / 3) (by positivity)).exists
      have := hfin n
      have hmeas : Tendsto (fun K => (lam n (Set.accumulate f K)).toReal) atTop
          (𝓝 ((lam n (⋃ i, f i)).toReal)) :=
        (ENNReal.tendsto_toReal (measure_ne_top _ _)).comp tendsto_measure_iUnion_accumulate
      obtain ⟨K0, hK0⟩ := Metric.tendsto_atTop.mp hmeas (δ / 3) (by positivity)
      refine ⟨K0, fun K hK => ?_⟩
      have h1 := h n _ (hacc K)
      have h2 := h n _ hU
      have h3 := hK0 K hK
      rw [Real.dist_eq] at h3 ⊢
      rw [abs_lt] at h3 ⊢
      rw [abs_le] at h1 h2
      constructor <;> linarith
    rw [ENNReal.tsum_eq_iSup_nat' (N := fun K => K + 1) (tendsto_add_atTop_nat 1)]
    simp only [hpart]
    exact tendsto_nhds_unique ((ENNReal.continuous_ofReal.tendsto _).comp htend)
      (tendsto_atTop_iSup hmonoK)
  refine ⟨Measure.ofMeasurable (fun C _ => ENNReal.ofReal (β C)) (by simp [hempty]) hsig, ⟨?_⟩,
    fun C hC => Measure.ofMeasurable_apply C hC⟩
  rw [Measure.ofMeasurable_apply _ MeasurableSet.univ]
  exact ENNReal.ofReal_lt_top
