-- Prove2me | solution 1 for BalancedAlgebra.gregarious_of_source_or_sink
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-09-14T15:45:18.699926+00:00
-- url     : https://prove2.me/submissions/99b57dc2-12e7-4740-9aae-fdfc88d4580e

import Mathlib
import Definitions.Def_BalancedAlgebra_core

set_option linter.unusedSectionVars false

namespace BAFix

open BalancedAlgebra BalancedAlgebra.PartialAlgebra

/-- Sources and sinks are gregarious, in any algebra. -/
theorem gregarious_of_source_or_sink {A : Type*} (P : PartialAlgebra A) (x : A)
    (hx : P.IsSource x ∨ P.IsSink x) : P.Gregarious x := by
  rcases hx with ⟨hu, hsrc⟩ | ⟨hv, hsnk⟩
  · rintro p q ⟨d, hd⟩ ⟨e, he⟩
    left
    have hp : p = x := hsrc p ⟨d, hd⟩
    rw [hp] at hd
    have hdx : d = x := hu x d hd
    refine ⟨e, ?_⟩
    rw [lprod_eq_some]
    exact ⟨d, by rw [hp]; exact hd, by rw [hdx]; exact he⟩
  · rintro p q ⟨d, hd⟩ ⟨e, he⟩
    right
    have hq : q = x := hsnk q ⟨e, he⟩
    rw [hq] at he
    have hex : e = x := hv x e he
    refine ⟨d, ?_⟩
    rw [rprod_eq_some]
    exact ⟨e, by rw [hq]; exact he, by rw [hex]; exact hd⟩

end BAFix

open BalancedAlgebra BalancedAlgebra.PartialAlgebra in
theorem solution {A : Type*} (P : PartialAlgebra A) (x : A)
    (hx : P.IsSource x ∨ P.IsSink x) : P.Gregarious x :=
  BAFix.gregarious_of_source_or_sink P x hx
