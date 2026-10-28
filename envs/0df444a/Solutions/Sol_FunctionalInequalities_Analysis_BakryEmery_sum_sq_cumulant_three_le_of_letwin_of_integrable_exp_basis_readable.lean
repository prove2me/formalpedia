-- Prove2me | solution 1 for FunctionalInequalities.Analysis.BakryEmery.sum_sq_cumulant_three_le_of_letwin_of_integrable_exp_basis_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T13:29:14.137331+00:00
-- url     : https://prove2.me/submissions/2d896bd3-a0dc-4279-b3a6-945b2438edb5

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Tensor_Coefficients
import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_Cumulant_Local
import Theorems.Thm_FunctionalInequalities_Analysis_BakryEmery_sum_sq_cumulant_three_le_of_letwin_of_integrable_exp_readable
import Theorems.Thm_FunctionalInequalities_Analysis_Tensor_sum_coordTensor_sq_eq_readable

section
noncomputable section
open Finset
open scoped RealInnerProductSpace
section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
theorem FunctionalInequalities.Analysis.Tensor.coordTensor_apply {n k : ℕ} (b : OrthonormalBasis (Fin n) ℝ E)
    (Φ : ContinuousMultilinearMap ℝ (fun _ : Fin k => E) ℝ) (i : Fin k → Fin n) :
    coordTensor b Φ i = Φ (fun j => b (i j)) := by
  rfl
end
end
end

open MeasureTheory Filter Topology
open scoped RealInnerProductSpace ContDiff
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
private theorem FunctionalInequalities.Analysis.BakryEmery.sum_pair_eq_sum_tensor {m : ℕ}
    (b : OrthonormalBasis (Fin m) ℝ E)
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin 2 => E) ℝ) :
    (∑ j, ∑ k, T ![b j, b k] ^ 2) =
      ∑ J : Fin 2 → Fin m, Analysis.Tensor.coordTensor b T J ^ 2 := by
  classical
  calc
    (∑ j, ∑ k, T ![b j, b k] ^ 2) =
        ∑ q : Fin m × Fin m, T ![b q.1, b q.2] ^ 2 :=
      (Fintype.sum_prod_type (fun q : Fin m × Fin m => T ![b q.1, b q.2] ^ 2)).symm
    _ = ∑ q : Fin m × Fin m,
        Analysis.Tensor.coordTensor b T ((finTwoArrowEquiv (Fin m)).symm q) ^ 2 := by
      apply Finset.sum_congr rfl
      intro q _hq
      rw [Analysis.Tensor.coordTensor_apply, finTwoArrowEquiv_symm_apply]
      have heq : (fun i => b (![q.1, q.2] i)) = ![b q.1, b q.2] := by
        ext i
        fin_cases i <;> rfl
      rw [heq]
    _ = _ := (finTwoArrowEquiv (Fin m)).symm.sum_comp
      (fun J => Analysis.Tensor.coordTensor b T J ^ 2)
/-- The same bound in any orthonormal basis (Hilbert–Schmidt norm is basis independent). -/
theorem solution (μ : Measure E) [IsProbabilityMeasure μ]
    {r : ℝ} (hr : 0 < r) (hexp : Integrable (fun x => Real.exp (r * ‖x‖)) μ)
    (hc : ∀ v : E, ∫ x, ⟪v, x⟫ ∂μ = 0)
    (hiso : ∀ v w : E, ∫ x, ⟪v, x⟫ * ⟪w, x⟫ ∂μ = ⟪v, w⟫)
    (hL : FunctionalInequalities.Analysis.BakryEmery.LetwinQuadraticBound μ) {m : ℕ} (b : OrthonormalBasis (Fin m) ℝ E) (u : E) :
    ∑ j, ∑ k, FunctionalInequalities.Analysis.BakryEmery.cumulant μ 3 ![u, b j, b k] ^ 2 ≤ 8 * ‖u‖ ^ 2 := by
  have hcons (a b : E) : Fin.cons u ![a, b] = ![u, a, b] := by
    ext i
    fin_cases i <;> rfl
  let T : ContinuousMultilinearMap ℝ (fun _ : Fin 2 => E) ℝ :=
    (FunctionalInequalities.Analysis.BakryEmery.cumulant μ 3).curryLeft u
  have hb : (∑ j, ∑ k, FunctionalInequalities.Analysis.BakryEmery.cumulant μ 3 ![u, b j, b k] ^ 2) =
      ∑ J : Fin 2 → Fin m, FunctionalInequalities.Analysis.Tensor.coordTensor b T J ^ 2 := by
    simpa only [T, ContinuousMultilinearMap.curryLeft_apply, hcons] using FunctionalInequalities.Analysis.BakryEmery.sum_pair_eq_sum_tensor b T
  have hs : (∑ j, ∑ k, FunctionalInequalities.Analysis.BakryEmery.cumulant μ 3
      ![u, stdOrthonormalBasis ℝ E j, stdOrthonormalBasis ℝ E k] ^ 2) =
      ∑ J : Fin 2 → Fin (Module.finrank ℝ E),
        FunctionalInequalities.Analysis.Tensor.coordTensor (stdOrthonormalBasis ℝ E) T J ^ 2 := by
    simpa only [T, ContinuousMultilinearMap.curryLeft_apply, hcons] using
      FunctionalInequalities.Analysis.BakryEmery.sum_pair_eq_sum_tensor (stdOrthonormalBasis ℝ E) T
  rw [hb, FunctionalInequalities.Analysis.Tensor.sum_coordTensor_sq_eq_readable b (stdOrthonormalBasis ℝ E) T, ← hs]
  exact FunctionalInequalities.Analysis.BakryEmery.sum_sq_cumulant_three_le_of_letwin_of_integrable_exp_readable μ hr hexp hc hiso hL u
