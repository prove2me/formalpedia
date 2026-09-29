-- Prove2me | solution 1 for CompetitivePaging.LowerBound.uncoveredProb_sum_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-28T23:44:58.020464+00:00
-- url     : https://prove2.me/submissions/37028b26-d617-44ea-93b0-33f785e0f4bb

import Mathlib
import Definitions.Def_KServer_model
import Definitions.Def_KServer_randomized
import Definitions.Def_CompetitivePaging_LowerBound_uncoveredProb

namespace CompetitivePaging.LowerBound

theorem aux_ups_unique_uncovered {n : ℕ} (hn : 2 ≤ n) {M : Type} [Fintype M]
    (hM : Fintype.card M = n) (f : Fin (n - 1) → M) (hf : Function.Injective f) :
    ∃ a : M, ∀ i : M, i ∉ Set.range f ↔ i = a := by
  classical
  have hc : ((Finset.univ.image f)ᶜ).card = 1 := by
    rw [Finset.card_compl, Finset.card_image_of_injective _ hf, Finset.card_univ,
      Fintype.card_fin, hM]
    omega
  obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hc
  refine ⟨a, fun i => ?_⟩
  have h := congrArg (i ∈ ·) ha
  simp only [Finset.mem_compl, Finset.mem_image, Finset.mem_univ, true_and,
    Finset.mem_singleton, eq_iff_iff] at h
  rw [← h]
  simp [Set.mem_range]

end CompetitivePaging.LowerBound

open CompetitivePaging.LowerBound

theorem solution (n : ℕ) (hn : 2 ≤ n) (M : Type) [MetricSpace M] [Fintype M]
    (hM : Fintype.card M = n) (A : KServer.RandomizedAlgorithm (n - 1) M) (σ : List M)
    (hinj : ∀ ω, Function.Injective ((A.alg ω).conf σ))
    (hmeas : ∀ i : M, @MeasurableSet A.ι A.ms {ω | i ∉ Set.range ((A.alg ω).conf σ)}) :
    ∑ i, uncoveredProb A σ i = 1 := by
  classical
  let _ := A.ms
  have := A.prob
  have key : ∀ ω, ∃ a : M, ∀ i : M, i ∉ Set.range ((A.alg ω).conf σ) ↔ i = a :=
    fun ω => aux_ups_unique_uncovered hn hM _ (hinj ω)
  have hdisj : Set.PairwiseDisjoint (↑(Finset.univ : Finset M))
      (fun i => {ω | i ∉ Set.range ((A.alg ω).conf σ)}) := by
    intro i _ j _ hij
    rw [Function.onFun, Set.disjoint_left]
    intro ω hi hj
    obtain ⟨a, ha⟩ := key ω
    exact hij (((ha i).1 hi).trans ((ha j).1 hj).symm)
  have hunion : (⋃ i ∈ (Finset.univ : Finset M),
      {ω | i ∉ Set.range ((A.alg ω).conf σ)}) = Set.univ := by
    ext ω
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq, Finset.mem_univ, exists_true_left,
      Set.mem_univ, iff_true]
    obtain ⟨a, ha⟩ := key ω
    exact ⟨a, (ha a).2 rfl⟩
  have hsum := MeasureTheory.measure_biUnion_finset (μ := A.μ) hdisj (fun i _ => hmeas i)
  rw [hunion, MeasureTheory.measure_univ] at hsum
  unfold uncoveredProb
  rw [← ENNReal.toReal_sum (fun i _ => MeasureTheory.measure_ne_top _ _), ← hsum]
  simp
