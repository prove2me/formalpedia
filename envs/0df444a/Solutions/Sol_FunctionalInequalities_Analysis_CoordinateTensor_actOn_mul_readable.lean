-- Prove2me | solution 1 for FunctionalInequalities.Analysis.CoordinateTensor.actOn_mul_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T13:26:43.113164+00:00
-- url     : https://prove2.me/submissions/0df989c3-ca40-4ce1-8319-27462f13d885

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Tensor_SlotAction

noncomputable section
open Matrix
section S3Bf3ASlotActionAlgebra
variable {n r : ℕ}
/-- A product of matrices acts as the composition at the same slot. -/
theorem solution (M N : Matrix (Fin n) (Fin n) ℝ) (s : Fin r) (T : (Fin r → Fin n) → ℝ) :
    FunctionalInequalities.Analysis.CoordinateTensor.actOn (M * N) s T = FunctionalInequalities.Analysis.CoordinateTensor.actOn M s (FunctionalInequalities.Analysis.CoordinateTensor.actOn N s T) := by
  classical
  funext J
  simp only [FunctionalInequalities.Analysis.CoordinateTensor.actOn]
  calc
    (∑ k, (M * N) (J s) k * T (Function.update J s k)) =
        ∑ k, (∑ l, M (J s) l * N l k) * T (Function.update J s k) := by
          apply Finset.sum_congr rfl
          intro k hk
          exact congrArg (fun x : ℝ => x * T (Function.update J s k))
            (Matrix.mul_apply (M := M) (N := N) (i := J s) (k := k))
    _ = ∑ k, ∑ l, (M (J s) l * N l k) *
          T (Function.update J s k) := by
          apply Finset.sum_congr rfl
          intro k hk
          rw [Finset.sum_mul]
    _ = ∑ k, ∑ l, (M (J s) k * N k l) *
          T (Function.update J s l) := by
          rw [Finset.sum_comm]
    _ = ∑ k, ∑ l, M (J s) k *
          (N (Function.update J s k s) l *
            T (Function.update (Function.update J s k) s l)) := by
          apply Finset.sum_congr rfl
          intro k hk
          apply Finset.sum_congr rfl
          intro l hl
          rw [Function.update_self, Function.update_idem]
          ring
    _ = ∑ k, M (J s) k *
          (∑ l, N (Function.update J s k s) l *
            T (Function.update (Function.update J s k) s l)) := by
          apply Finset.sum_congr rfl
          intro k hk
          rw [Finset.mul_sum]
