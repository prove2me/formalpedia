-- Prove2me | solution 1 for BraidsLinksMCG.puncturedPlaneGroup_equiv_free
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-21T21:44:27.207761+00:00
-- url     : https://prove2.me/submissions/8bf3b790-e5c6-4f59-ac14-c4a457218790
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_BraidsLinksMCG_puncturedPlaneGroup_succ_step
import Mathlib
import Definitions.Def_BraidsLinksMCG_ConfigSpace

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option linter.all false

open BraidsLinksMCG

namespace BaseSol

/-- With no punctures the "punctured plane" is the whole plane. -/
def zeroHomeo : PuncturedPlane 0 ≃ₜ ℂ where
  toFun z := z.1
  invFun z := ⟨z, fun j => absurd j.isLt (by omega)⟩
  left_inv z := by apply Subtype.ext; rfl
  right_inv z := rfl
  continuous_toFun := continuous_subtype_val
  continuous_invFun := Continuous.subtype_mk continuous_id _

instance : SimplyConnectedSpace (PuncturedPlane 0) :=
  (zeroHomeo.toHomotopyEquiv).simplyConnectedSpace

theorem base : Nonempty (PuncturedPlaneGroup 0 ≃* FreeGroup (Fin 0)) := by
  have h1 : Subsingleton (PuncturedPlaneGroup 0) := by infer_instance
  have h2 : Subsingleton (FreeGroup (Fin 0)) := by infer_instance
  exact ⟨{ toFun := fun _ => 1, invFun := fun _ => 1,
            left_inv := fun _ => Subsingleton.elim _ _,
            right_inv := fun _ => Subsingleton.elim _ _,
            map_mul' := fun _ _ => Subsingleton.elim _ _ }⟩

end BaseSol

theorem _root_.solution (n : ℕ) :
    Nonempty (PuncturedPlaneGroup n ≃* FreeGroup (Fin n)) := by
  induction n with
  | zero => exact BaseSol.base
  | succ m ih => exact BraidsLinksMCG.puncturedPlaneGroup_succ_step m ih

#print axioms solution
