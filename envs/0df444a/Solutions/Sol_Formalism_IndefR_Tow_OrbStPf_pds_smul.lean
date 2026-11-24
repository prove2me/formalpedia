-- Prove2me | solution 1 for Formalism.IndefR.Tow.OrbStPf.pds_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T09:43:46.656828+00:00
-- url     : https://prove2.me/submissions/3ccaa713-086d-43ba-adea-08124d20bcf2

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_SobolevIteration_DifferentiableUpdate
import Theorems.Thm_Formalism_IndefR_Tow_OrbStPf_pds_nil
import Theorems.Thm_Formalism_IndefR_Tow_OrbStPf_pds_cons
import Theorems.Thm_Formalism_IndefR_Tow_OrbStPf_differentiable_pds
import Theorems.Thm_Formalism_IndefR_Tow_OrbStPf_pd_smul
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
theorem _root_.solution (L : List (Fin N)) (c : ℝ) {f : (Fin N → ℝ) → H} (hf : ContDiff ℝ ∞ f) :
    pds L (fun p => c • f p) = fun p => c • pds L f p := by
  induction L with
  | nil => rfl
  | cons i L ih =>
    simp only [pds_cons]
    rw [ih, pd_smul i c (differentiable_pds L hf)]
end Formalism.IndefR.Tow.OrbStPf
