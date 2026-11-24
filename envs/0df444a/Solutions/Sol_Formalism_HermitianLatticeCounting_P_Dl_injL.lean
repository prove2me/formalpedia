-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.Dl_injL
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:02:23.616151+00:00
-- url     : https://prove2.me/submissions/d8131fce-c80f-4d2f-90ea-fb1ecce083a4

import Definitions.Def_Formalism_FlagUnipotentLattices_MemOfOrthogonalAnisotropic
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_ExistsHasLeadingCoeffOfMemSpanBelow
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_e_mem_Xa
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_mem_Xa_iff
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_gram_inj
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
    {x : V} (hx : x ∈ F.Xa j) (h : ∀ u ∈ F'.Xa j, H.B x u = 0) : x = 0 := by
  rw [Dl_eq] at hD
  obtain ⟨c, rfl⟩ := ((mem_Xa_iff F) hj).1 hx
  have hc := gram_inj H (fun a : Fin j => F.e (Fin.castLE (hj.trans (Nat.le_succ r)) a))
    (fun b : Fin j => F'.e (Fin.castLE (hj.trans (Nat.le_succ r)) b)) hD c
    (fun b => h _ ((e_mem_Xa F') ⟨b.val, by have := b.isLt; omega⟩ b.isLt))
  rw [hc]
  simp
end Formalism.HermitianLatticeCounting.P
