-- Prove2me | solution 1 for Formalism.Q3.cc_not_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:02:23.624854+00:00
-- url     : https://prove2.me/submissions/c0120186-647d-48b0-a340-70b34b00fcb7

import Mathlib
import Definitions.Def_Formalism_CMTypeGalois_StatementGroup
import Definitions.Def_Formalism_CMTypeGalois_CMTypeFrobenius_KroneckerMeaning

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.Q3
open ZMod
namespace Formalism.Q3
theorem _root_.solution (a b : Gal3) (j : Fin 3) (ha : a j = 1) (hb : b j = 1) :
    cc ∉ Subgroup.closure ({a, b} : Set Gal3) := by
  intro h
  have hle : Subgroup.closure ({a, b} : Set Gal3) ≤ (Pi.evalMonoidHom (fun _ : Fin 3 => ℤˣ) j).ker := by
    rw [Subgroup.closure_le]
    rintro x (rfl | rfl)
    · rw [SetLike.mem_coe, MonoidHom.mem_ker, Pi.evalMonoidHom_apply]; exact ha
    · rw [SetLike.mem_coe, MonoidHom.mem_ker, Pi.evalMonoidHom_apply]; exact hb
  have := hle h
  rw [MonoidHom.mem_ker, Pi.evalMonoidHom_apply] at this
  have h' : (-1 : ℤˣ) = 1 := this
  exact absurd h' (by decide)
end Formalism.Q3
