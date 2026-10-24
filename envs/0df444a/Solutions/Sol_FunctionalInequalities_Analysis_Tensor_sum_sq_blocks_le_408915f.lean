-- Prove2me | solution 1 for FunctionalInequalities.Analysis.Tensor.sum_sq_blocks_le_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T15:00:13.850159+00:00
-- url     : https://prove2.me/submissions/aff339db-0071-4da7-961e-72797f4abe5c

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_Coordinate
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_Symmetrization
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Operator.LinearIsometry
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.GroupTheory.Perm.Basic

noncomputable section
open Finset
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
private theorem FunctionalInequalities.Analysis.Tensor.blocks_injective {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] {d : ℕ} (hd : 0 < d) :
    Function.Injective
      (fun p : κ × (Fin d → ι) => fun k => some (p.1, p.2 k)) := by
  rintro ⟨i, j⟩ ⟨i', j'⟩ h
  have hp (k : Fin d) : (i, j k) = (i', j' k) := by
    exact Option.some.inj (congrFun h k)
  have hi : i = i' := by
    exact congrArg (fun q : κ × ι => q.1) (hp ⟨0, hd⟩)
  have hj : j = j' := by
    funext k
    exact congrArg (fun q : κ × ι => q.2) (hp k)
  cases hi
  cases hj
  rfl
section FiniteIndex
variable {ι κ : Type*}
variable [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
namespace FunctionalInequalities.Analysis.Tensor
end FunctionalInequalities.Analysis.Tensor
open FunctionalInequalities.Analysis.Tensor in
/-- **Disjoint copy blocks** (BKL Proposition 7.1, the Hilbert–Schmidt estimate after (112)). For `d > 0` the map `(i, j) ↦ (fun k => some (i, j k))` is injective,
so the block entries of `A` are a subfamily of all entries. -/
theorem solution
    {d : ℕ} (hd : 0 < d) (A : (Fin d → Option (κ × ι)) → ℝ) :
    ∑ i : κ, ∑ j : Fin d → ι, A (fun k => some (i, j k)) ^ 2 ≤ ∑ J, A J ^ 2 := by
    let f : κ × (Fin d → ι) → (Fin d → Option (κ × ι)) :=
      fun p k => some (p.1, p.2 k)
    have hf : Function.Injective f := by
      dsimp [f]
      exact blocks_injective hd
    have hsum :
        (Finset.univ : Finset (κ × (Fin d → ι))).sum (fun p => A (f p) ^ 2) =
          (Finset.univ.image f).sum (fun J => A J ^ 2) := by
      rw [Finset.sum_image]
      intro a ha b hb hab
      exact hf hab
    calc
      ∑ i : κ, ∑ j : Fin d → ι, A (fun k => some (i, j k)) ^ 2 =
          ∑ p : κ × (Fin d → ι), A (f p) ^ 2 := by
        simp only [f, Fintype.sum_prod_type]
      _ = (Finset.univ.image f).sum (fun J => A J ^ 2) := hsum
      _ ≤ (Finset.univ : Finset (Fin d → Option (κ × ι))).sum (fun J => A J ^ 2) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro J hJ
          simp
        · intro J hJ hJ'
          positivity
