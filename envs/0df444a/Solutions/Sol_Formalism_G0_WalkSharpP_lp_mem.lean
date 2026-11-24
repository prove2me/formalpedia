-- Prove2me | solution 1 for Formalism.G0.WalkSharpP.lp_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:13:47.012854+00:00
-- url     : https://prove2.me/submissions/8ca35395-ff8a-4e11-8c69-fc1a89869abf

import Definitions.Def_Formalism_SubspaceCounting_Statement
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_WalkSharp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Formalism Formalism.G0
open Formalism.G0.WalkSharpP
variable {R X : Type} [CommRing R] [AddCommGroup X] [Module R X] {V : ℕ}
namespace Formalism.G0.WalkSharpP
theorem _root_.solution (y : Fin V → Module.End R X) (M : Submodule R X) (hM : ∀ u, ∀ x ∈ M, y u x ∈ M)
    (l : List (Fin V)) (e : Fin V → ℕ) : ∀ x ∈ M, lp y l e x ∈ M := by

  have hpow : ∀ u (n : ℕ), ∀ x ∈ M, (y u ^ n) x ∈ M := by
    intro u n
    induction n with
    | zero => intro x hx; rw [pow_zero]; exact hx
    | succ n ihn => intro x hx; rw [pow_succ]; exact ihn _ (hM u x hx)
  induction l with
  | nil => intro x hx; simpa [lp] using hx
  | cons u l ih =>
    intro x hx
    simp only [lp, List.map_cons, List.prod_cons] at ih ⊢
    exact hpow u (e u) _ (ih x hx)
end Formalism.G0.WalkSharpP
