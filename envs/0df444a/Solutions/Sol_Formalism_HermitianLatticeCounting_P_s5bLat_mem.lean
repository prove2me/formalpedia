-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.s5bLat_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:31:45.423231+00:00
-- url     : https://prove2.me/submissions/1cd932de-baa2-4be6-bfd5-9c005477ca6c

import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_LatticeSumBounds
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_SumComplexEmbeddingsEqSumInfinitePlace

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module Matrix Formalism.HermitianLatticeCounting.LatticeSumBounds
open scoped BigOperators ComplexConjugate
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
open NumberField
open NumberField
variable {E : Type} [Field E] [NumberField E]
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution (hc : ∀ w : InfinitePlace E, w.IsComplex) (x : s5bV E) :
    x ∈ integerEmbeddingLattice hc ↔ ∃ a : 𝓞 E, x = complexEmbeddingVector (a : E) := by
  classical
  have key : ∀ a : 𝓞 E, (complexSpaceMixedEquivCLM hc).symm
      (mixedEmbedding E (a : E)) = complexEmbeddingVector (a : E) := by
    intro a
    ext w
    rfl
  constructor
  · intro hx
    have hx' : (complexSpaceMixedEquivCLM hc) x ∈
        mixedEmbedding.integerLattice E := hx
    obtain ⟨a, ha⟩ := LinearMap.mem_range.mp hx'
    refine ⟨a, ?_⟩
    have h2 : (complexSpaceMixedEquivCLM hc).symm (mixedEmbedding E (a : E)) = x :=
      (complexSpaceMixedEquivCLM hc).symm_apply_eq.mpr ha
    rw [← h2, key a]
  · rintro ⟨a, rfl⟩
    have h3 : (complexSpaceMixedEquivCLM hc) (complexEmbeddingVector (a : E)) ∈
        mixedEmbedding.integerLattice E := by
      rw [← key a, ContinuousLinearEquiv.apply_symm_apply]
      exact LinearMap.mem_range.mpr ⟨a, rfl⟩
    exact h3
end Formalism.HermitianLatticeCounting.P
