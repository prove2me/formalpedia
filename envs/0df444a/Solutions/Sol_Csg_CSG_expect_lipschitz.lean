-- Prove2me | solution 1 for Csg.CSG.expect_lipschitz
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T22:38:55.196205+00:00
-- url     : https://prove2.me/submissions/96212237-0f58-43b2-9a3f-0eb339f05df2

import Definitions.Def_Csg_Basic
import Definitions.Def_Csg_CsgMonotone
import Theorems.Thm_Csg_CSG_expect_le_add_of_forall_le

set_option autoImplicit true
open Csg
open Csg.CSG
variable {S A1 A2 : Type*} [Fintype S] [Fintype A1] [Fintype A2] [Nonempty A1] [Nonempty A2]
  [DecidableEq A1] [DecidableEq A2]
variable (C : CSG S A1 A2)
namespace Csg.CSG
theorem _root_.solution {s : S} {a1 : A1} {a2 : A2} {v w : S → ℝ} {ε : ℝ} (hε : 0 ≤ ε)
    (h : ∀ s', |v s' - w s'| ≤ ε) : |C.expect s a1 a2 v - C.expect s a1 a2 w| ≤ ε := by
  have hub : ∀ s', v s' ≤ w s' + ε := fun s' => by linarith [(abs_le.mp (h s')).2]
  have hlb : ∀ s', w s' ≤ v s' + ε := fun s' => by linarith [(abs_le.mp (h s')).1]
  have h1 : C.expect s a1 a2 v ≤ C.expect s a1 a2 w + ε := C.expect_le_add_of_forall_le hε hub
  have h2 : C.expect s a1 a2 w ≤ C.expect s a1 a2 v + ε := C.expect_le_add_of_forall_le hε hlb
  exact abs_le.mpr ⟨by linarith, by linarith⟩
end Csg.CSG
