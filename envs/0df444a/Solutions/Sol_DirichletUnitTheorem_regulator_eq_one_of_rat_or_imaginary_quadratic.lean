-- Prove2me | solution 1 for DirichletUnitTheorem.regulator_eq_one_of_rat_or_imaginary_quadratic
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T02:20:10.751632+00:00
-- url     : https://prove2.me/submissions/00a0757f-b0f2-4b6a-a904-4690ea12d382

import Mathlib
open NumberField

theorem solution (K : Type*) [Field K] [NumberField K]
    (hK : Module.finrank ℚ K = 1 ∨ (Module.finrank ℚ K = 2 ∧ IsTotallyComplex K)) :
    Units.regulator K = 1 := by
  classical
  have h0 : Units.rank K = 0 := by
    rw [Units.rank, InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces]
    rw [← NumberField.nrRealPlaces_eq_zero_iff, ← InfinitePlace.card_add_two_mul_card_eq_rank] at hK
    omega
  obtain ⟨w'⟩ : Nonempty (InfinitePlace K) := inferInstance
  have hsub : IsEmpty {w : InfinitePlace K // w ≠ w'} := by
    have hc : Fintype.card {w : InfinitePlace K // w ≠ w'} = 0 := by
      rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq]
      unfold Units.rank at h0
      omega
    exact Fintype.card_eq_zero_iff.mp hc
  have : IsEmpty (Fin (Units.rank K)) := by rw [h0]; infer_instance
  rw [Units.regulator_eq_det K w' (Equiv.equivOfIsEmpty _ _), Matrix.det_isEmpty, abs_one]
