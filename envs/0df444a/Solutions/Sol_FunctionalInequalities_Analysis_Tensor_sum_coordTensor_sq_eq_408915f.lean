-- Prove2me | solution 1 for FunctionalInequalities.Analysis.Tensor.sum_coordTensor_sq_eq_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T14:50:38.323291+00:00
-- url     : https://prove2.me/submissions/e9db7775-ab91-4145-ae2f-3772ebdc0b9a

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
import Theorems.Thm_FunctionalInequalities_Analysis_Tensor_apply_eq_sum_coordTensor_408915f

section
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
end
end
end
end
end

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
/-- The change-of-basis matrix between product bases is column-orthonormal:
`∑ᵢ (∏ⱼ ⟪b' (l j), b (i j)⟫) (∏ⱼ ⟪b' (l' j), b (i j)⟫) = δ_{l l'}`. -/
private lemma FunctionalInequalities.Analysis.Tensor.sum_prod_inner_mul_prod_inner {n n' k : ℕ} (b : OrthonormalBasis (Fin n) ℝ E)
    (b' : OrthonormalBasis (Fin n') ℝ E) (l l' : Fin k → Fin n') :
    ∑ i : Fin k → Fin n, (∏ j, ⟪b' (l j), b (i j)⟫) * ∏ j, ⟪b' (l' j), b (i j)⟫ =
      if l = l' then 1 else 0 := by
  classical
  calc
    ∑ i : Fin k → Fin n, (∏ j, ⟪b' (l j), b (i j)⟫) * ∏ j, ⟪b' (l' j), b (i j)⟫
        = ∑ i : Fin k → Fin n, ∏ j, ⟪b' (l j), b (i j)⟫ * ⟪b' (l' j), b (i j)⟫ := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.prod_mul_distrib]
    _ = ∏ j : Fin k, ∑ m : Fin n, ⟪b' (l j), b m⟫ * ⟪b' (l' j), b m⟫ := by
          rw [Fintype.prod_sum]
    _ = ∏ j : Fin k, ⟪b' (l j), b' (l' j)⟫ := by
          refine Finset.prod_congr rfl fun j _ => ?_
          rw [← b.sum_inner_mul_inner (b' (l j)) (b' (l' j))]
          refine Finset.sum_congr rfl fun m _ => ?_
          rw [real_inner_comm (b' (l' j)) (b m)]
    _ = ∏ j : Fin k, (if l j = l' j then (1 : ℝ) else 0) := by
          refine Finset.prod_congr rfl fun j _ => ?_
          exact orthonormal_iff_ite.mp b'.orthonormal (l j) (l' j)
    _ = if l = l' then 1 else 0 := by
          rw [Finset.prod_boole]
          simp [funext_iff]
namespace FunctionalInequalities.Analysis.Tensor
end FunctionalInequalities.Analysis.Tensor
open FunctionalInequalities.Analysis.Tensor in
/-- The sum of squares of the coefficients of a multilinear form does not depend on the
orthonormal basis. -/
theorem solution {n n' k : ℕ} (b : OrthonormalBasis (Fin n) ℝ E)
    (b' : OrthonormalBasis (Fin n') ℝ E)
    (Φ : ContinuousMultilinearMap ℝ (fun _ : Fin k => E) ℝ) :
    ∑ i : Fin k → Fin n, FunctionalInequalities.Analysis.Tensor.coordTensor b Φ i ^ 2 = ∑ l : Fin k → Fin n', FunctionalInequalities.Analysis.Tensor.coordTensor b' Φ l ^ 2 := by
  classical
  set c := FunctionalInequalities.Analysis.Tensor.coordTensor b' Φ
  set M : (Fin k → Fin n) → (Fin k → Fin n') → ℝ := fun i l => ∏ j, ⟪b' (l j), b (i j)⟫
  have hexp (i : Fin k → Fin n) : FunctionalInequalities.Analysis.Tensor.coordTensor b Φ i = ∑ l, c l * M i l := by
    rw [FunctionalInequalities.Analysis.Tensor.coordTensor_apply]
    exact FunctionalInequalities.Analysis.Tensor.apply_eq_sum_coordTensor_408915f b' Φ (fun j => b (i j))
  calc
    ∑ i : Fin k → Fin n, FunctionalInequalities.Analysis.Tensor.coordTensor b Φ i ^ 2
        = ∑ i : Fin k → Fin n, ∑ l, ∑ l', c l * c l' * (M i l * M i l') := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [hexp, sq, Finset.sum_mul_sum]
          refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun l' _ => ?_
          ring
    _ = ∑ l, ∑ l', c l * c l' * ∑ i : Fin k → Fin n, M i l * M i l' := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun l _ => ?_
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun l' _ => ?_
          rw [Finset.mul_sum]
    _ = ∑ l, ∑ l', c l * c l' * (if l = l' then 1 else 0) := by
          refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun l' _ => ?_
          rw [sum_prod_inner_mul_prod_inner b b' l l']
    _ = ∑ l : Fin k → Fin n', c l ^ 2 := by
          refine Finset.sum_congr rfl fun l _ => ?_
          simp [sq]
