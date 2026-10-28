-- Prove2me | solution 1 for FunctionalInequalities.Analysis.CoordinateTensor.inner_actOn_left_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T13:26:45.416007+00:00
-- url     : https://prove2.me/submissions/b9b66a19-4f24-46e1-88bd-2a8a1fb0530a

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Tensor_SlotAction

noncomputable section
open Matrix
section S3Bf3ASlotActionAlgebra
variable {n r : ℕ}
/-- The slot action of a symmetric matrix is self-adjoint for `inner`. -/
theorem solution (M : Matrix (Fin n) (Fin n) ℝ) (hM : M.IsSymm) (s : Fin r)
    (T S : (Fin r → Fin n) → ℝ) : FunctionalInequalities.Analysis.CoordinateTensor.inner (FunctionalInequalities.Analysis.CoordinateTensor.actOn M s T) S = FunctionalInequalities.Analysis.CoordinateTensor.inner T (FunctionalInequalities.Analysis.CoordinateTensor.actOn M s S) := by
  classical
  let f : ((Fin r → Fin n) × Fin n) → ((Fin r → Fin n) × Fin n) :=
    fun x => (Function.update x.1 s x.2, x.1 s)
  have hf : Function.Involutive f := by
    rintro ⟨J, k⟩
    dsimp [f]
    apply Prod.ext
    · rw [Function.update_idem, Function.update_eq_self]
    · exact Function.update_self s k J
  let e : Equiv.Perm ((Fin r → Fin n) × Fin n) := hf.toPerm
  have heval (J : Fin r → Fin n) (k : Fin n) :
      e (J, k) = (Function.update J s k, J s) := by
    rfl
  calc
    FunctionalInequalities.Analysis.CoordinateTensor.inner (FunctionalInequalities.Analysis.CoordinateTensor.actOn M s T) S =
        ∑ J, ∑ k, M (J s) k * T (Function.update J s k) * S J := by
          unfold FunctionalInequalities.Analysis.CoordinateTensor.inner FunctionalInequalities.Analysis.CoordinateTensor.actOn
          apply Finset.sum_congr rfl
          intro J hJ
          rw [Finset.sum_mul]
    _ = ∑ x : (Fin r → Fin n) × Fin n,
          M (x.1 s) x.2 * T (Function.update x.1 s x.2) * S x.1 := by
          symm
          exact Fintype.sum_prod_type' (γ := ℝ)
            (α₁ := Fin r → Fin n) (α₂ := Fin n)
            (fun J k => M (J s) k * T (Function.update J s k) * S J)
    _ = ∑ x : (Fin r → Fin n) × Fin n,
          T x.1 * M (x.1 s) x.2 * S (Function.update x.1 s x.2) := by
          refine Fintype.sum_equiv (M := ℝ) e
            (fun x : (Fin r → Fin n) × Fin n =>
              M (x.1 s) x.2 * T (Function.update x.1 s x.2) * S x.1)
            (fun x : (Fin r → Fin n) × Fin n =>
              T x.1 * M (x.1 s) x.2 * S (Function.update x.1 s x.2)) ?_
          rintro ⟨J, k⟩
          simp only [heval, Function.update_self, Function.update_idem,
            Function.update_eq_self]
          rw [hM.apply (J s) k]
          ring
    _ = ∑ J, ∑ k, T J * M (J s) k * S (Function.update J s k) := by
          exact Fintype.sum_prod_type' (γ := ℝ)
            (α₁ := Fin r → Fin n) (α₂ := Fin n)
            (fun J k => T J * M (J s) k * S (Function.update J s k))
    _ = FunctionalInequalities.Analysis.CoordinateTensor.inner T (FunctionalInequalities.Analysis.CoordinateTensor.actOn M s S) := by
          unfold FunctionalInequalities.Analysis.CoordinateTensor.inner FunctionalInequalities.Analysis.CoordinateTensor.actOn
          apply Finset.sum_congr rfl
          intro J hJ
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro k hk
          ring
