-- Prove2me | solution 1 for BKAR.partialDeriv_of_hasFDerivAt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:20:58.970813+00:00
-- url     : https://prove2.me/submissions/69b9541a-6602-48ae-bb61-ec7ed473408b

import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Pi
import Definitions.Def_BKAR_Interpolation
import Definitions.Def_BKAR_PartialDeriv
import Theorems.Thm_BKAR_updateCoord_self
import Theorems.Thm_BKAR_updateCoord_same_value
import Theorems.Thm_BKAR_updateCoord_update_same
import Theorems.Thm_BKAR_edgeBasis_self
import Theorems.Thm_BKAR_Forest_paramValue_of_mem
import Theorems.Thm_BKAR_Forest_pathMin_cons
import Theorems.Thm_BKAR_Forest_pathMin_nil
attribute [local simp] BKAR.Forest.paramValue_of_mem
attribute [local simp] BKAR.Forest.pathMin_cons
attribute [local simp] BKAR.Forest.pathMin_nil


attribute [local simp] BKAR.updateCoord_self
attribute [local simp] BKAR.updateCoord_same_value
attribute [local simp] BKAR.updateCoord_update_same
attribute [local simp] BKAR.edgeBasis_self

set_option autoImplicit false
open BKAR
variable {V : Type*} [DecidableEq V]
namespace BKAR
theorem _root_.solution [Fintype V] (e : Edge V)
    {ρ : (Edge V → ℝ) → ℝ} {x : Edge V → ℝ}
    {ρ' : (Edge V → ℝ) →L[ℝ] ℝ}
    (hρ : HasFDerivAt ρ ρ' x) :
    partialDeriv e ρ x = ρ' (edgeBasis e) := by
  have hupdate :
      HasDerivAt (updateCoord x e) (edgeBasis e) (x e) := by
    simpa [updateCoord] using! hasDerivAt_update (𝕜 := ℝ) x e (x e)
  have hcomp :
      HasDerivAt (ρ ∘ updateCoord x e)
        (ρ' (edgeBasis e)) (x e) :=
    hρ.comp_hasDerivAt_of_eq (x e) hupdate
      (updateCoord_same_value x e).symm
  rw [partialDeriv]
  exact hcomp.deriv
end BKAR
