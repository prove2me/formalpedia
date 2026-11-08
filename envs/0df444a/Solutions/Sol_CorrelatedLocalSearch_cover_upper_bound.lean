-- Prove2me | solution 1 for CorrelatedLocalSearch.cover_upper_bound
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T21:53:37.924041+00:00
-- url     : https://prove2.me/submissions/b562f5f2-ec8f-46c2-9d70-fb08384090f1

import Mathlib
import Definitions.Def_CorrelatedLocalSearch_SourceClass

set_option autoImplicit false

open MeasureTheory

open CorrelatedLocalSearch in
theorem solution (k : ℕ) (s D : ℝ) (hD : 1 ≤ D) (ν : Measure (ℕ → Fin k))
    (hν : ν ∈ SourceClass k s D) (E : Set (ℕ → Fin k)) (B : Finset (List (Fin k)))
    (hB : E ⊆ ⋃ w ∈ B, cyl w) :
    ν E ≤ ENNReal.ofReal (D * ∑ w ∈ B, refMass k w ^ s) := by
  have hnn : ∀ w : List (Fin k), 0 ≤ D * refMass k w ^ s := by
    intro w
    refine mul_nonneg (by linarith) (Real.rpow_nonneg ?_ s)
    unfold refMass
    positivity
  calc ν E ≤ ν (⋃ w ∈ B, cyl w) := measure_mono hB
    _ ≤ ∑ w ∈ B, ν (cyl w) := measure_biUnion_finset_le B _
    _ ≤ ∑ w ∈ B, ENNReal.ofReal (D * refMass k w ^ s) := Finset.sum_le_sum (fun w _ => hν.2 w)
    _ = ENNReal.ofReal (∑ w ∈ B, D * refMass k w ^ s) :=
        (ENNReal.ofReal_sum_of_nonneg (fun w _ => hnn w)).symm
    _ = ENNReal.ofReal (D * ∑ w ∈ B, refMass k w ^ s) := by rw [Finset.mul_sum]
