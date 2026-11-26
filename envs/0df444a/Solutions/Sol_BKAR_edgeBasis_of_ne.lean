-- Prove2me | solution 1 for BKAR.edgeBasis_of_ne
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:19:46.877211+00:00
-- url     : https://prove2.me/submissions/087b06ce-228b-462c-8500-2d561e3bd529

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
theorem _root_.solution {e e' : Edge V} (hne : e' ≠ e) :
    edgeBasis e e' = 0 := by
  simpa [edgeBasis] using
    Pi.single_eq_of_ne (M := fun _ : Edge V => ℝ) hne (1 : ℝ)
end BKAR
