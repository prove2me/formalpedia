-- Prove2me | solution 1 for Formalism.IndefR.Tow.OrbStPf.update_add_single
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:07:21.836263+00:00
-- url     : https://prove2.me/submissions/c47b7cc4-bea1-4118-b2f3-b330cca98409

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_SobolevIteration_DifferentiableUpdate
import Theorems.Thm_Formalism_IndefR_Tow_OrbStPf_pds_nil
import Theorems.Thm_Formalism_IndefR_Tow_OrbStPf_pds_cons
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.IndefR.Tow.OrbStPf.pds_nil
attribute [local simp] Formalism.IndefR.Tow.OrbStPf.pds_cons

set_option autoImplicit false
noncomputable section
open scoped ContDiff
open Formalism Formalism.IndefR Formalism.IndefR.Tow Formalism.IndefR.Tow.OrbStPf
variable {N : ℕ} {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
namespace Formalism.IndefR.Tow.OrbStPf
theorem _root_.solution {i j : Fin N} (hij : i ≠ j) (r : Fin N → ℝ) (s t : ℝ) :
    Function.update (r + t • Pi.single i 1) j s = Function.update r j s + t • Pi.single i 1 := by
  funext k
  by_cases hk : k = j <;> simp [Function.update_apply, hk, Pi.single_apply, Ne.symm hij]
end Formalism.IndefR.Tow.OrbStPf
