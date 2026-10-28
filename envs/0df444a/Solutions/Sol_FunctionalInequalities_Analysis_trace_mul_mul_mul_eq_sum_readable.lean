-- Prove2me | solution 1 for FunctionalInequalities.Analysis.trace_mul_mul_mul_eq_sum_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T13:29:49.602787+00:00
-- url     : https://prove2.me/submissions/38c387af-c13d-4422-b87b-9da43f6ca92c

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Matrix_Trace_Algebra

open Matrix
section TraceFourProduct
private theorem FunctionalInequalities.Analysis.reverse_triple_sum {n : ℕ} (f : Fin n → Fin n → Fin n → ℝ) :
    (∑ d, ∑ c, ∑ b, f b c d) = ∑ b, ∑ c, ∑ d, f b c d := by
  calc
    (∑ d, ∑ c, ∑ b, f b c d) = ∑ d, ∑ b, ∑ c, f b c d := by
      apply Finset.sum_congr rfl
      intro d _
      exact Finset.sum_comm
    _ = ∑ b, ∑ d, ∑ c, f b c d := Finset.sum_comm
    _ = ∑ b, ∑ c, ∑ d, f b c d := by
      apply Finset.sum_congr rfl
      intro b _
      exact Finset.sum_comm
/-- The trace of a four-fold product of square matrices as one sum over index quadruples:
`tr(A H B J) = ∑ (A_{ab} B_{cd}) (H_{bc} J_{da})`. -/
theorem solution {n : ℕ} (A H B J : Matrix (Fin n) (Fin n) ℝ) :
    (A * H * B * J).trace =
      ∑ q : Fin n × Fin n × Fin n × Fin n,
        (A q.1 q.2.1 * B q.2.2.1 q.2.2.2) *
          (H q.2.1 q.2.2.1 * J q.2.2.2 q.1) := by
  simp only [Fintype.sum_prod_type, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]
  simp_rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a _
  calc
    (∑ d, ∑ c, ∑ b, A a b * H b c * B c d * J d a) =
        ∑ b, ∑ c, ∑ d, A a b * H b c * B c d * J d a :=
      FunctionalInequalities.Analysis.reverse_triple_sum _
    _ = ∑ b, ∑ c, ∑ d, (A a b * B c d) * (H b c * J d a) := by
      apply Finset.sum_congr rfl
      intro b _
      apply Finset.sum_congr rfl
      intro c _
      apply Finset.sum_congr rfl
      intro d _
      ring
