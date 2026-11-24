-- Prove2me | solution 1 for Formalism.IndefR.Tow.OrbStPf.pd_clm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:07:21.876619+00:00
-- url     : https://prove2.me/submissions/5c17247e-93d8-4f33-b961-fb647fb83d2f

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
theorem _root_.solution (i : Fin N) (A : H →L[ℝ] H) {f : (Fin N → ℝ) → H} (hf : Differentiable ℝ f) :
    pd i (fun p => A (f p)) = fun p => A (pd i f p) := by
  funext p
  have h := (A.hasFDerivAt.comp p (hf p).hasFDerivAt).fderiv
  simp only [pd]
  rw [show (fun q => A (f q)) = A ∘ f from rfl, h]
  rfl
end Formalism.IndefR.Tow.OrbStPf
