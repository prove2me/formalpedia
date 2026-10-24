-- Prove2me | solution 1 for FunctionalInequalities.Analysis.Tensor.apply_eq_sum_coordTensor_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T14:49:49.459039+00:00
-- url     : https://prove2.me/submissions/7cf946a2-d9de-485e-a993-9f92fce1be02

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_Coefficients
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_Coordinate
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_Multilinear
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_Symmetrization
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Module.Multilinear.Curry
import Mathlib.Analysis.Normed.Operator.LinearIsometry
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.GroupTheory.Perm.Basic

noncomputable section
open Finset
open scoped RealInnerProductSpace
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities FunctionalInequalities.Analysis
section
namespace FunctionalInequalities.Analysis.Tensor
end FunctionalInequalities.Analysis.Tensor
open FunctionalInequalities FunctionalInequalities.Analysis FunctionalInequalities.Analysis.Tensor
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
namespace FunctionalInequalities.Analysis.Tensor
end FunctionalInequalities.Analysis.Tensor
open FunctionalInequalities.Analysis.Tensor in
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
        exact multilinear_basis_expand b Φ (fun j l => ⟪b l, h j⟫)
      _ = ∑ i : Fin k → Fin n,
          FunctionalInequalities.Analysis.Tensor.coordTensor b Φ i * ∏ j, ⟪b (i j), h j⟫ := by
        simp [FunctionalInequalities.Analysis.Tensor.coordTensor_apply, smul_eq_mul, mul_comm]
