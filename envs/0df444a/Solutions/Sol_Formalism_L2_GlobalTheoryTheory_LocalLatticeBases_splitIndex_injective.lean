-- Prove2me | solution 1 for Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.splitIndex_injective
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:14:33.850449+00:00
-- url     : https://prove2.me/submissions/9d7c7b35-fa5e-41b4-bb87-3c56aaaad5ad

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_GL6_LinearIndependentProdRenameOfCard

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory.LocalLatticeBases
open MvPolynomial
variable {K : Type*} [Field K] {S₁ S₂ : Type*}
namespace Formalism.L2.GlobalTheoryTheory.LocalLatticeBases
theorem _root_.solution {ι σ : Type} (i : ι) : Function.Injective (sumComplementToProduct (σ := σ) i) := by
  intro x y h
  rcases x with x | ⟨⟨j, hj⟩, x⟩ <;> rcases y with y | ⟨⟨j', hj'⟩, y⟩ <;>
    simp only [sumComplementToProduct, Sum.elim_inl, Sum.elim_inr, Prod.mk.injEq] at h
  all_goals first
    | exact absurd h.1.symm hj'
    | exact absurd h.1 hj
    | simp_all
end Formalism.L2.GlobalTheoryTheory.LocalLatticeBases
