-- Prove2me | solution 1 for CompetitivePaging.LowerBound.expCost_append_ge_uncoveredProb
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T00:57:50.958254+00:00
-- url     : https://prove2.me/submissions/99676d90-5bef-4bcf-9ee9-3829d91aa937

import Mathlib
import Definitions.Def_KServer_model
import Definitions.Def_KServer_randomized
import Definitions.Def_CompetitivePaging_LowerBound_uncoveredProb

namespace CompetitivePaging.LowerBound

open MeasureTheory

lemma aux_ecu_moveCost_nonneg {k : ℕ} {M : Type} [MetricSpace M]
    (C C' : KServer.Config k M) : 0 ≤ KServer.moveCost C C' :=
  Finset.sum_nonneg (fun _ _ => dist_nonneg)

lemma aux_ecu_cost_nonneg {k : ℕ} {M : Type} [MetricSpace M]
    (B : KServer.OnlineAlgorithm k M) (σ : List M) : 0 ≤ B.cost σ :=
  Finset.sum_nonneg (fun _ _ => aux_ecu_moveCost_nonneg _ _)

lemma aux_ecu_cost_append {k : ℕ} {M : Type} [MetricSpace M]
    (B : KServer.OnlineAlgorithm k M) (σ : List M) (i : M) :
    B.cost (σ ++ [i]) = B.cost σ + KServer.moveCost (B.conf σ) (B.conf (σ ++ [i])) := by
  unfold KServer.OnlineAlgorithm.cost
  rw [List.length_append, List.length_singleton, Finset.sum_range_succ]
  congr 1
  · apply Finset.sum_congr rfl
    intro j hj
    rw [Finset.mem_range] at hj
    rw [List.take_append_of_le_length (by omega), List.take_append_of_le_length (by omega)]
  · rw [List.take_append_of_le_length le_rfl, List.take_length,
      List.take_of_length_le (by simp)]

lemma aux_ecu_moveCost_ge {k : ℕ} {M : Type} [MetricSpace M]
    (hd : ∀ x y : M, x ≠ y → dist x y = 1)
    (B : KServer.OnlineAlgorithm k M) (σ : List M) (i : M)
    (h : i ∉ Set.range (B.conf σ)) :
    1 ≤ KServer.moveCost (B.conf σ) (B.conf (σ ++ [i])) := by
  obtain ⟨s, hs⟩ := B.serves σ i
  have hne : B.conf σ s ≠ B.conf (σ ++ [i]) s := by
    rw [hs]; intro heq; exact h ⟨s, heq⟩
  unfold KServer.moveCost
  calc (1:ℝ) = dist (B.conf σ s) (B.conf (σ ++ [i]) s) := (hd _ _ hne).symm
    _ ≤ ∑ j, dist (B.conf σ j) (B.conf (σ ++ [i]) j) :=
        Finset.single_le_sum (f := fun j => dist (B.conf σ j) (B.conf (σ ++ [i]) j))
          (fun _ _ => dist_nonneg) (Finset.mem_univ s)

end CompetitivePaging.LowerBound

open CompetitivePaging.LowerBound
open MeasureTheory

theorem solution {k : ℕ} (M : Type) [MetricSpace M]
    (hd : ∀ x y : M, x ≠ y → dist x y = 1) (A : KServer.RandomizedAlgorithm k M)
    (σ : List M) (i : M)
    (hmeas : @MeasurableSet A.ι A.ms {ω | i ∉ Set.range ((A.alg ω).conf σ)}) :
    A.expCost σ + ENNReal.ofReal (uncoveredProb A σ i) ≤ A.expCost (σ ++ [i]) := by
  let _ := A.ms
  have := A.prob
  set S := {ω | i ∉ Set.range ((A.alg ω).conf σ)} with hS
  have hpt : ∀ ω, ENNReal.ofReal ((A.alg ω).cost σ) + S.indicator 1 ω ≤
      ENNReal.ofReal ((A.alg ω).cost (σ ++ [i])) := by
    intro ω
    rw [aux_ecu_cost_append, ENNReal.ofReal_add (aux_ecu_cost_nonneg _ _)
      (aux_ecu_moveCost_nonneg _ _)]
    gcongr
    by_cases hω : ω ∈ S
    · rw [Set.indicator_of_mem hω]
      simpa using aux_ecu_moveCost_ge hd _ _ _ hω
    · rw [Set.indicator_of_notMem hω]; exact zero_le
  have hmf : Measurable fun ω => ENNReal.ofReal ((A.alg ω).cost σ) :=
    ENNReal.measurable_ofReal.comp (A.meas σ)
  unfold KServer.RandomizedAlgorithm.expCost uncoveredProb
  rw [ENNReal.ofReal_toReal (measure_ne_top _ _)]
  calc ∫⁻ ω, ENNReal.ofReal ((A.alg ω).cost σ) ∂A.μ + A.μ S
      = ∫⁻ ω, ENNReal.ofReal ((A.alg ω).cost σ) ∂A.μ + ∫⁻ ω, S.indicator 1 ω ∂A.μ := by
        rw [lintegral_indicator_one hmeas]
    _ = ∫⁻ ω, (ENNReal.ofReal ((A.alg ω).cost σ) + S.indicator 1 ω) ∂A.μ :=
        (lintegral_add_left hmf _).symm
    _ ≤ _ := lintegral_mono hpt
