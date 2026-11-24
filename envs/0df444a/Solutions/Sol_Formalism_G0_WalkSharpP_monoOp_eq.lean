-- Prove2me | solution 1 for Formalism.G0.WalkSharpP.monoOp_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:20:46.416273+00:00
-- url     : https://prove2.me/submissions/680b6a51-087c-4d34-9d6e-8a11afee4012

import Definitions.Def_Formalism_SubspaceCounting_Statement
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_WalkSharp
import Theorems.Thm_Formalism_G0_WalkSharpP_list_prod_smul

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
theorem _root_.solution (π : R) (y : Fin V → Module.End R X) (m : ℕ) (S : Fin V → ℕ)
    (e : Fin V → Bool) :
    monoOp π y m S e = π ^ (∑ u, if e u then 0 else S u) •
      lp y (List.finRange V) (fun u => if e u then m else 0) := by

  unfold monoOp
  rw [show ((List.finRange V).map fun v => if e v then y v ^ m else (π ^ S v) • (1 : Module.End R X)) =
      (List.finRange V).map (fun v => (π ^ (if e v then 0 else S v)) • (y v ^ (if e v then m else 0))) by
    congr 1
    funext v
    by_cases hv : e v <;> simp [hv]]
  rw [list_prod_smul]
  refine congrArg₂ (· • ·) ?_ rfl
  rw [← Fin.prod_univ_def, Finset.prod_pow_eq_pow_sum]
end Formalism.G0.WalkSharpP
