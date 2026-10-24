-- Prove2me | solution 1 for FunctionalInequalities.Analysis.Tensor.image_mem_powersetCard_of_mem_fixingOutside_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T14:59:24.850191+00:00
-- url     : https://prove2.me/submissions/e6531f5b-c055-4176-aab8-22fd9fb5d0e6

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_Symmetrization
import Mathlib.Analysis.InnerProductSpace.Basic
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
variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
namespace FunctionalInequalities.Analysis.Tensor
end FunctionalInequalities.Analysis.Tensor
open FunctionalInequalities.Analysis.Tensor in
/-- Permutations fixing everything outside `Q` map `A ⊆ Q` to a subset of `Q` of the same size. -/
theorem solution {A Q : Finset Ω} (hAQ : A ⊆ Q)
    {σ : Equiv.Perm Ω} (hσ : σ ∈ FunctionalInequalities.Analysis.Tensor.fixingOutside Q) : A.image σ ∈ Q.powersetCard A.card := by
    refine Finset.mem_powersetCard.mpr ?_
    constructor
    · intro x hx
      rcases Finset.mem_image.mp hx with ⟨a, ha, rfl⟩
      by_contra hnot
      have hxx : σ (σ a) = σ a := by
        exact (show ∀ y, y ∉ Q → σ y = y from by
          simpa [FunctionalInequalities.Analysis.Tensor.fixingOutside] using hσ) (σ a) hnot
      have heq : σ a = a := σ.injective hxx
      have haQ : a ∈ Q := hAQ ha
      exact hnot (by simpa [heq] using haQ)
    · exact Finset.card_image_of_injective _ σ.injective
