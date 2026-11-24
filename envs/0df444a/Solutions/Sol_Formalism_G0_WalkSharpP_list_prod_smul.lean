-- Prove2me | solution 1 for Formalism.G0.WalkSharpP.list_prod_smul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:13:46.555949+00:00
-- url     : https://prove2.me/submissions/a35b6424-fa4f-420f-a4df-5cdaca6a285f

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
theorem _root_.solution (l : List (Fin V)) (r : Fin V → R) (A : Fin V → Module.End R X) :
    (l.map fun u => r u • A u).prod = (l.map r).prod • (l.map A).prod := by

  induction l with
  | nil => simp
  | cons u l ih =>
    simp only [List.map_cons, List.prod_cons, ih]
    rw [smul_mul_assoc, mul_smul_comm, smul_smul]
end Formalism.G0.WalkSharpP
