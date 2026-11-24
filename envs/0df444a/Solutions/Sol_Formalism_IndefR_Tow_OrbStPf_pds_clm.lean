-- Prove2me | solution 1 for Formalism.IndefR.Tow.OrbStPf.pds_clm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T09:30:35.037814+00:00
-- url     : https://prove2.me/submissions/c862bfbb-6fb0-446c-8815-eaa3282fb190

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_SobolevIteration_DifferentiableUpdate
import Theorems.Thm_Formalism_IndefR_Tow_OrbStPf_pds_nil
import Theorems.Thm_Formalism_IndefR_Tow_OrbStPf_pds_cons
import Theorems.Thm_Formalism_IndefR_Tow_OrbStPf_differentiable_pds
import Theorems.Thm_Formalism_IndefR_Tow_OrbStPf_pd_clm
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
theorem _root_.solution (L : List (Fin N)) (A : H →L[ℝ] H) {f : (Fin N → ℝ) → H} (hf : ContDiff ℝ ∞ f) :
    pds L (fun p => A (f p)) = fun p => A (pds L f p) := by
  induction L with
  | nil => rfl
  | cons i L ih =>
    simp only [pds_cons]
    rw [ih, pd_clm i A (differentiable_pds L hf)]
end Formalism.IndefR.Tow.OrbStPf
