-- Prove2me | solution 1 for Formalism.G0.WalkSharpP.lp_single
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:13:47.65827+00:00
-- url     : https://prove2.me/submissions/aada3568-c978-4526-a62a-7e761bcc3a01

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
theorem _root_.solution (y : Fin V → Module.End R X) (v : Fin V) (l : List (Fin V)) (hl : l.Nodup) :
    lp y l (fun u => if u = v then 1 else 0) = if v ∈ l then y v else 1 := by

  induction l with
  | nil => simp [lp]
  | cons u l ih =>
    rw [List.nodup_cons] at hl
    have h2 := ih hl.2
    simp only [lp] at h2 ⊢
    rw [List.map_cons, List.prod_cons, h2]
    by_cases huv : u = v
    · subst huv
      simp [hl.1]
    · simp [huv, Ne.symm huv]
end Formalism.G0.WalkSharpP
