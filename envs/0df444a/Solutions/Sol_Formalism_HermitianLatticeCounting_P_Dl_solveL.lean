-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.Dl_solveL
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:03:22.45758+00:00
-- url     : https://prove2.me/submissions/0986445e-a999-4958-a069-f82b93ca4210

import Definitions.Def_Formalism_FlagUnipotentLattices_MemOfOrthogonalAnisotropic
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_ExistsHasLeadingCoeffOfMemSpanBelow
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_mem_Xa_iff
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_gram_solve
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_Dl_eq

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
theorem _root_.solution (F F' : FlagD H r) {j : ℕ} (hj : j ≤ r) (hD : Dl F F' j (hj.trans (Nat.le_succ r)) ≠ 0)
    (t : Fin j → K) : ∃ x ∈ F.Xa j, ∀ b : Fin j, H.B x (F'.e (Fin.castLE (hj.trans (Nat.le_succ r)) b)) = t b := by
  rw [Dl_eq] at hD
  obtain ⟨c, hc⟩ := gram_solve H (fun a : Fin j => F.e (Fin.castLE (hj.trans (Nat.le_succ r)) a))
    (fun b : Fin j => F'.e (Fin.castLE (hj.trans (Nat.le_succ r)) b)) hD t
  exact ⟨_, ((mem_Xa_iff F) hj).2 ⟨c, rfl⟩, hc⟩
end Formalism.HermitianLatticeCounting.P
