-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.splitResidueTrace
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:02:22.622214+00:00
-- url     : https://prove2.me/submissions/493b9c98-3afa-4b6f-a142-eda6d292a5b8

import Definitions.Def_Formalism_FlagUnipotentLattices_CardSubmodulesAndLinearEquivBounds
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_LatticeSumBounds

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
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution : ResidueSplit := by
  intro k A _ _ _ _ ε hε
  have hsa : ∀ a : A, star a = a ↔ (ε a).1 = (ε a).2 := by
    intro a
    constructor
    · intro h
      have h0 := hε a
      rw [h] at h0
      have h1 := congrArg Prod.fst h0
      simpa using h1
    · intro h
      apply ε.injective
      rw [hε]
      ext <;> simp [h]
  refine ⟨?_, ?_, ?_⟩
  · rw [Nat.card_congr ε.toEquiv, Nat.card_prod, sq]
  · apply Nat.card_congr
    exact {
      toFun := fun a => (ε a.1).1
      invFun := fun x => ⟨ε.symm (x, x), (hsa _).mpr (by simp)⟩
      left_inv := fun a => by
        apply Subtype.ext
        apply ε.injective
        simp only [RingEquiv.apply_symm_apply]
        ext
        · rfl
        · exact (hsa a.1).mp a.2
      right_inv := fun x => by simp }
  · intro a ha
    refine ⟨ε.symm ((ε a).1, 0), ?_⟩
    apply ε.injective
    rw [map_add, hε, RingEquiv.apply_symm_apply]
    ext
    · simp
    · simp [(hsa a).mp ha]
end Formalism.HermitianLatticeCounting.P
