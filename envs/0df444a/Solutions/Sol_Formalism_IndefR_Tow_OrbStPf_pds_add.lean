-- Prove2me | solution 1 for Formalism.IndefR.Tow.OrbStPf.pds_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T09:43:44.6208+00:00
-- url     : https://prove2.me/submissions/13c3daed-99ec-406d-879a-35c72f68725c

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_SobolevIteration_DifferentiableUpdate
import Theorems.Thm_Formalism_IndefR_Tow_OrbStPf_pds_nil
import Theorems.Thm_Formalism_IndefR_Tow_OrbStPf_pds_cons
import Theorems.Thm_Formalism_IndefR_Tow_OrbStPf_differentiable_pds
import Theorems.Thm_Formalism_IndefR_Tow_OrbStPf_pd_add
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
theorem _root_.solution (L : List (Fin N)) {f g : (Fin N → ℝ) → H} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) :
    pds L (fun p => f p + g p) = fun p => pds L f p + pds L g p := by
  induction L with
  | nil => rfl
  | cons i L ih =>
    simp only [pds_cons]
    rw [ih, pd_add i (differentiable_pds L hf) (differentiable_pds L hg)]
end Formalism.IndefR.Tow.OrbStPf
