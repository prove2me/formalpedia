-- Prove2me | solution 1 for FunctionalInequalities.Analysis.Tensor.apply_eq_sum_coordTensor_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T13:26:22.556368+00:00
-- url     : https://prove2.me/submissions/398f5e94-6c5e-4aca-8cf3-867ab56a795c

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Tensor_Coefficients

noncomputable section
open Finset
open scoped RealInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
theorem FunctionalInequalities.Analysis.Tensor.coordTensor_apply {n k : ℕ} (b : OrthonormalBasis (Fin n) ℝ E)
    (Φ : ContinuousMultilinearMap ℝ (fun _ : Fin k => E) ℝ) (i : Fin k → Fin n) :
    coordTensor b Φ i = Φ (fun j => b (i j)) := by
  rfl
private lemma FunctionalInequalities.Analysis.Tensor.multilinear_basis_expand {n k : ℕ}
    (b : OrthonormalBasis (Fin n) ℝ E)
    (Φ : ContinuousMultilinearMap ℝ (fun _ : Fin k => E) ℝ)
    (c : Fin k → Fin n → ℝ) :
    Φ (fun j => ∑ l, c j l • b l) =
      ∑ i : Fin k → Fin n, (∏ j, c j (i j)) • Φ (fun j => b (i j)) := by
  classical
  rw [Φ.map_sum]
  simp_rw [Φ.map_smul_univ]
/-- Expansion of a multilinear map in an orthonormal basis. -/
theorem solution {n k : ℕ} (b : OrthonormalBasis (Fin n) ℝ E)
    (Φ : ContinuousMultilinearMap ℝ (fun _ : Fin k => E) ℝ) (h : Fin k → E) :
    Φ h = ∑ i : Fin k → Fin n, FunctionalInequalities.Analysis.Tensor.coordTensor b Φ i * ∏ j, ⟪b (i j), h j⟫ := by
    classical
    have hh :
        h = (fun j => ∑ l : Fin n, ⟪b l, h j⟫ • b l) := by
      funext j
      symm
      exact b.sum_repr' (h j)
    calc
      Φ h = Φ (fun j => ∑ l : Fin n, ⟪b l, h j⟫ • b l) := by
        exact congrArg (fun x => Φ x) hh
      _ = ∑ i : Fin k → Fin n,
          (∏ j, ⟪b (i j), h j⟫) • Φ (fun j => b (i j)) := by
        exact FunctionalInequalities.Analysis.Tensor.multilinear_basis_expand b Φ (fun j l => ⟪b l, h j⟫)
      _ = ∑ i : Fin k → Fin n,
          FunctionalInequalities.Analysis.Tensor.coordTensor b Φ i * ∏ j, ⟪b (i j), h j⟫ := by
        simp [FunctionalInequalities.Analysis.Tensor.coordTensor_apply, smul_eq_mul, mul_comm]
