-- Prove2me | solution 1 for BraidsLinksMCG.puncturedPlaneGroup_free_on_standardGen
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-21T22:49:00.969169+00:00
-- url     : https://prove2.me/submissions/4b0556e8-a0db-4780-821f-d636ba24b92a
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_BraidsLinksMCG_puncturedPlaneGroup_free_on_standardGen_step
import Mathlib
import Definitions.Def_BraidsLinksMCG_ConfigSpace
import Definitions.Def_BraidsLinksMCG_StandardLoops

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

theorem base : ∃ e : PuncturedPlaneGroup 0 ≃* FreeGroup (Fin 0),
    ∀ j : Fin 0, e (standardGen 0 j) = FreeGroup.of j := by
  have h1 : Subsingleton (PuncturedPlaneGroup 0) := by infer_instance
  have h2 : Subsingleton (FreeGroup (Fin 0)) := by infer_instance
  refine ⟨{ toFun := fun _ => 1, invFun := fun _ => 1,
            left_inv := fun _ => Subsingleton.elim _ _,
            right_inv := fun _ => Subsingleton.elim _ _,
            map_mul' := fun _ _ => Subsingleton.elim _ _ }, ?_⟩
  intro j
  exact absurd j.isLt (by omega)

end BaseSol

theorem _root_.solution (n : ℕ) :
    ∃ e : PuncturedPlaneGroup n ≃* FreeGroup (Fin n),
      ∀ j : Fin n, e (standardGen n j) = FreeGroup.of j := by
  induction n with
  | zero => exact BaseSol.base
  | succ m ih => exact BraidsLinksMCG.puncturedPlaneGroup_free_on_standardGen_step m ih

#print axioms solution
