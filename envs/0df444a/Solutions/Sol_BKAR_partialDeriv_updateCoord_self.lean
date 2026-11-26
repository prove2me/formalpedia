-- Prove2me | solution 1 for BKAR.partialDeriv_updateCoord_self
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:15:21.441211+00:00
-- url     : https://prove2.me/submissions/826c0ced-7f57-46cf-8c2a-28bf0d8218ae

import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Pi
import Definitions.Def_BKAR_Interpolation
import Definitions.Def_BKAR_PartialDeriv
import Theorems.Thm_BKAR_updateCoord_self
import Theorems.Thm_BKAR_updateCoord_update_same
import Theorems.Thm_BKAR_Forest_paramValue_of_mem
import Theorems.Thm_BKAR_Forest_pathMin_cons
import Theorems.Thm_BKAR_Forest_pathMin_nil
attribute [local simp] BKAR.Forest.paramValue_of_mem
attribute [local simp] BKAR.Forest.pathMin_cons
attribute [local simp] BKAR.Forest.pathMin_nil


attribute [local simp] BKAR.updateCoord_self
attribute [local simp] BKAR.updateCoord_update_same

set_option autoImplicit false
open BKAR
variable {V : Type*} [DecidableEq V]
namespace BKAR
theorem _root_.solution (e : Edge V)
    (ρ : (Edge V → ℝ) → ℝ) (x : Edge V → ℝ) (s : ℝ) :
    partialDeriv e ρ (updateCoord x e s) =
      deriv (fun t : ℝ => ρ (updateCoord x e t)) s := by
  rw [partialDeriv, updateCoord_self]
  apply congrArg (fun f : ℝ → ℝ => deriv f s)
  funext t
  rw [updateCoord_update_same]
end BKAR
