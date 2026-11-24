-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.finrank_compl
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:55:46.836313+00:00
-- url     : https://prove2.me/submissions/fe618a17-0e9c-430e-9aa9-9b6138b97c2a

import Definitions.Def_Formalism_FlagUnipotentLattices_MemOfOrthogonalAnisotropic
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_ExistsHasLeadingCoeffOfMemSpanBelow
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_finrank_Xa
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_finrank_X

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.HermitianLatticeCounting.S6
open scoped BigOperators
open Matrix
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
variable {K : Type} [Field K] [StarRing K] {V : Type} [AddCommGroup V] [Module K V]
  {H : HermSpace K V} {r : ℕ}
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution [FiniteDimensional K V] (F : FlagD H r) {j : ℕ} (hj : j ≤ r) (I : Submodule K V)
    (h1 : F.X = F.Xa j ⊔ I) (h2 : I ⊓ F.Xa j = ⊥) : Module.finrank K I = r - j := by
  have := Submodule.finrank_sup_add_finrank_inf_eq (F.Xa j) I
  rw [← h1, inf_comm, h2, finrank_bot, (finrank_X F), (finrank_Xa F) hj] at this
  omega
end Formalism.HermitianLatticeCounting.P
