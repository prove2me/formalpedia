-- Prove2me | solution 1 for FunctionalInequalities.Analysis.Tensor.image_mem_powersetCard_of_mem_fixingOutside_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T13:29:03.517432+00:00
-- url     : https://prove2.me/submissions/8f5e61f7-0b52-489b-994b-2c09b47bd3f1

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Tensor_Symmetrization

noncomputable section
open Finset
variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
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
