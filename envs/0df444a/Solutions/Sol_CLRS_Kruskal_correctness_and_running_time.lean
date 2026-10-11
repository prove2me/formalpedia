-- Prove2me | solution 1 for CLRS.Kruskal.correctness_and_running_time
-- status  : ACCEPTED   (prove)
-- author  : @lunjia
-- created : 2026-10-11T00:08:30.224719+00:00
-- url     : https://prove2.me/submissions/9a075d8d-ca89-4653-aefd-3e3d037b03ad

import Definitions.Def_SubmissionAnalysis_Kruskal
import Theorems.Thm_KruskalAnalysis_call_contract


section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true



/-!
Supplemental analysis for the Algo2Lean CLRS formalization series.
This file proves a uniform-constant corollary of the exact bound;
it does not change the algorithm or its generated definitions.
-/
namespace CLRS.Kruskal

open Algo2LeanGenerated



private theorem bound_le_scale (vertices edges : Nat) :
    KruskalAnalysis.runtimeBound vertices edges ≤ 18 * runtimeScale vertices edges := by
  unfold KruskalAnalysis.runtimeBound SortIndicesAnalysis.runtimeBound runtimeScale
  have hsort : 2 * edges * (3 * (edges + 1).log2 + 2) ≤
      edges * (18 * (edges + 1).log2 + 4) := by
    calc
      _ = edges * (6 * (edges + 1).log2 + 4) := by
        simp [Nat.mul_add, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
      _ ≤ _ := Nat.mul_le_mul_left _ (by omega)
  have hwork : edges * (10 * Algo2Lean.Ackermann.alpha vertices + 14) ≤
      edges * (18 * Algo2Lean.Ackermann.alpha vertices + 14) :=
    Nat.mul_le_mul_left _ (by omega)
  calc
    _ ≤ edges * (18 * (edges + 1).log2 + 4) + vertices + 2 +
        edges * (18 * Algo2Lean.Ackermann.alpha vertices + 14) := by omega
    _ ≤ 18 * (vertices + 1) +
        edges * (18 * (edges + 1).log2 + 18 * Algo2Lean.Ackermann.alpha vertices + 18) := by
      simp only [Nat.mul_add]
      omega
    _ = _ := by simp [Nat.mul_add, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]

/-- One positive constant works for every well-formed input. The same Call
returns minimum-spanning-forest flags, preserves the caller's storage,
allocates the output freshly and records its clock increments. -/
theorem correctness_and_running_time :
    ∃ C : Nat, 0 < C ∧
      ∀ (heap : Heap) (size count : Int) (sources targets weights : SeqRef),
        Algo.kruskal.kruskal.ValidInput heap (size, sources, targets, weights, count) →
        KruskalInput.WellFormed size count (heap.read sources) (heap.read targets) →
        ∃ final chosen selected,
          Algo.kruskal.kruskal.Call heap (size, sources, targets, weights, count) final chosen ∧
          Algo2Lean.Kruskal.MinimumSpanningForest
            (KruskalInput.edges (heap.read sources) (heap.read targets) (heap.read weights) count)
            selected ∧
          KruskalAnalysis.Flags (final.read chosen) selected ∧
          heap.Footprint final [] [] [] ∧
          heap.nextRef ≤ chosen ∧ chosen < final.nextRef ∧
          heap.Increments final (heap.cost final) ∧
          KruskalAnalysis.runtime (heap.cost final) ≤ C * runtimeScale size.toNat count.toNat := by
  refine ⟨18, by omega, ?_⟩
  intro heap size count sources targets weights valid wellFormed
  obtain ⟨final, chosen, selected, call, forest, flags, frame, fresh, allocated, increments, cost⟩ :=
    KruskalAnalysis.call_contract heap size count sources targets weights valid wellFormed
  exact ⟨final, chosen, selected, call, forest, flags, frame, fresh, allocated, increments,
    Nat.le_trans cost (bound_le_scale size.toNat count.toNat)⟩

end CLRS.Kruskal

end

set_option autoImplicit false
theorem solution :
    Exists.{1} fun C =>
      LT.lt.{0} (0 : Nat) C ∧
        ∀ (heap : Algo2LeanGenerated.Heap) (size count : Int)
          (sources targets weights : Algo2LeanGenerated.SeqRef),
          Algo.kruskal.kruskal.ValidInput heap
              (Prod.mk.{0, 0} size
                (Prod.mk.{0, 0} sources (Prod.mk.{0, 0} targets (Prod.mk.{0, 0} weights count)))) →
            KruskalInput.WellFormed size count (heap.read sources) (heap.read targets) →
              Exists.{1} fun final =>
                Exists.{1} fun chosen =>
                  Exists.{1} fun selected =>
                    Algo.kruskal.kruskal.Call heap
                        (Prod.mk.{0, 0} size
                          (Prod.mk.{0, 0} sources
                            (Prod.mk.{0, 0} targets (Prod.mk.{0, 0} weights count))))
                        final chosen ∧
                      Algo2Lean.Kruskal.MinimumSpanningForest
                          (KruskalInput.edges (heap.read sources) (heap.read targets)
                            (heap.read weights) count)
                          selected ∧
                        KruskalAnalysis.Flags (final.read chosen) selected ∧
                          heap.Footprint final List.nil.{0} List.nil.{0} List.nil.{0} ∧
                            LE.le.{0} heap.nextRef chosen ∧
                              LT.lt.{0} chosen final.nextRef ∧
                                heap.Increments final (heap.cost final) ∧
                                  LE.le.{0} (KruskalAnalysis.runtime (heap.cost final))
                                    (HMul.hMul.{0, 0, 0} C
                                      (CLRS.Kruskal.runtimeScale size.toNat count.toNat)) :=
  CLRS.Kruskal.correctness_and_running_time
