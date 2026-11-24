-- Prove2me | solution 1 for Formalism.HermitianLatticesTheory.neighbourConstruct_avoid
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:53:59.375275+00:00
-- url     : https://prove2.me/submissions/82851870-d266-4c97-af67-b38cb8278938

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_NeighbourConstruct
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_DualBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_NeighbourBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_NeighbourConstruct

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open nonZeroDivisors
open Formalism Formalism.HermitianLatticesTheory
variable {R : Type*} [CommRing R]
namespace Formalism.HermitianLatticesTheory
theorem _root_.solution {A B C : Ideal R} (hA : A.IsMaximal) (hB : B.IsMaximal)
    (hC : C.IsMaximal) (hAB : A ≠ B) (hAC : A ≠ C) : ∃ s ∈ A, s ∉ B ∧ s ∉ C := by
  by_contra H
  push Not at H
  have hsub : (A : Set R) ⊆ (B : Set R) ∪ C := by
    intro s hs
    by_cases hsB : s ∈ B
    · exact Or.inl hsB
    · exact Or.inr (H s hs hsB)
  rcases Ideal.subset_union.mp hsub with h1 | h1
  · exact hAB (hA.eq_of_le hB.ne_top h1)
  · exact hAC (hA.eq_of_le hC.ne_top h1)
end Formalism.HermitianLatticesTheory
