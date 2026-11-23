-- Prove2me | solution 1 for Formalism.IndefR.Tow.OrbStPf.pd_hasDerivAt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:15:58.424692+00:00
-- url     : https://prove2.me/submissions/73fa434e-6ea1-4d13-9365-c032722d9383

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
theorem _root_.solution (i : Fin N) {f : (Fin N → ℝ) → H} (p : Fin N → ℝ) (hf : DifferentiableAt ℝ f p) :
    HasDerivAt (fun t : ℝ => f (p + t • Pi.single i 1)) (pd i f p) 0 := by
  have h1 : HasDerivAt (fun t : ℝ => p + t • (Pi.single i 1 : Fin N → ℝ)) (Pi.single i 1) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (Pi.single i (1 : ℝ) : Fin N → ℝ)).const_add p
  have h2 : HasFDerivAt f (fderiv ℝ f (p + (0 : ℝ) • Pi.single i 1)) (p + (0 : ℝ) • Pi.single i 1) := by
    simpa using hf.hasFDerivAt
  have h3 := h2.comp_hasDerivAt (0 : ℝ) h1
  simpa [pd, Function.comp_def] using h3
end Formalism.IndefR.Tow.OrbStPf
