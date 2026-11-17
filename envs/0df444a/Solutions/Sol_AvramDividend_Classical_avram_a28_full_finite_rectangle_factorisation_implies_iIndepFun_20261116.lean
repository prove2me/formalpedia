-- Prove2me | solution 1 for AvramDividend.Classical.avram_a28_full_finite_rectangle_factorisation_implies_iIndepFun_20261116
-- status  : ACCEPTED   (disprove)
-- author  : @garyholm
-- created : 2026-11-16T15:03:28.629014+00:00
-- url     : https://prove2.me/submissions/f15c4e85-c59a-440d-8310-4daf575bb054

import Mathlib
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators
noncomputable section

theorem solution : ¬ (∀ {Ω E : Type} [MeasurableSpace Ω] [MeasurableSpace E]
    (P : Measure Ω) (n : ℕ) (Y : ℕ → Ω → E),
    (∀ (A : Fin n → Set E),
      (∀ i, MeasurableSet (A i)) →
      P {ω : Ω | ∀ i : Fin n, Y i.val ω ∈ A i} =
        ∏ i : Fin n, P (Y i.val ⁻¹' A i)) →
    iIndepFun (fun i : Fin n => Y i.val) P) := by
  intro H
  let P : Measure Unit := (2 : ℝ≥0∞) • Measure.dirac ()
  have hF : ∀ (A : Fin 1 → Set Unit), (∀ i, MeasurableSet (A i)) →
      P {ω : Unit | ∀ i : Fin 1, (fun (_ : ℕ) (_ : Unit) => ()) i.val ω ∈ A i} =
        ∏ i : Fin 1, P ((fun (_ : ℕ) (_ : Unit) => ()) i.val ⁻¹' A i) := by
    intro A _
    rw [Fin.prod_univ_one]
    congr 1
    ext ω
    simp [Fin.forall_fin_one]
  have hI := H P 1 (fun _ _ => ()) hF
  have h0 := (iIndepFun_iff_measure_inter_preimage_eq_mul.mp hI) ∅ (sets := fun _ => Set.univ)
    (fun _ _ => MeasurableSet.univ)
  simp [P] at h0
