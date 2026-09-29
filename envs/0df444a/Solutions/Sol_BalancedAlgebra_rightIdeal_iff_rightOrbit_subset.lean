-- Prove2me | solution 1 for BalancedAlgebra.rightIdeal_iff_rightOrbit_subset
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-09-14T15:44:34.227002+00:00
-- url     : https://prove2.me/submissions/401f6011-7911-4ab2-aaa8-855f9c91f116

import Mathlib
import Definitions.Def_BalancedAlgebra_core

set_option linter.unusedSectionVars false

namespace BAFix

open BalancedAlgebra BalancedAlgebra.PartialAlgebra

/-- A subset is a right ideal exactly when it is closed under right orbits. -/
theorem rightIdeal_iff_rightOrbit_subset {A : Type*} (P : PartialAlgebra A) (B : Set A) :
    P.RightIdeal B ↔ ∀ b ∈ B, P.rightOrbit b ⊆ B := by
  constructor
  · intro h b hb c hc
    obtain ⟨y, hy⟩ := hc
    exact h b y c hb hy
  · intro h a b c ha hop
    exact h a ha ⟨b, hop⟩

end BAFix

open BalancedAlgebra BalancedAlgebra.PartialAlgebra in
theorem solution {A : Type*} (P : PartialAlgebra A) (B : Set A) :
    P.RightIdeal B ↔ ∀ b ∈ B, P.rightOrbit b ⊆ B :=
  BAFix.rightIdeal_iff_rightOrbit_subset P B
