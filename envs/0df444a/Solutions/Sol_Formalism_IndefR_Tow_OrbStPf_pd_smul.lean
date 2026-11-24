-- Prove2me | solution 1 for Formalism.IndefR.Tow.OrbStPf.pd_smul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:07:21.892067+00:00
-- url     : https://prove2.me/submissions/f03d1ec0-feaf-49e8-9f8f-59df335926f2

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
theorem _root_.solution (i : Fin N) (c : ℝ) {f : (Fin N → ℝ) → H} (hf : Differentiable ℝ f) :
    pd i (fun p => c • f p) = fun p => c • pd i f p := by
  funext p
  simp only [pd]
  have h := ((hf p).hasFDerivAt.const_smul c).fderiv
  exact congrArg (fun L : (Fin N → ℝ) →L[ℝ] H => L (Pi.single i 1)) h
end Formalism.IndefR.Tow.OrbStPf
