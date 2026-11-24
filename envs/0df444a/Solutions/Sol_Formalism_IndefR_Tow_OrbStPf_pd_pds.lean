-- Prove2me | solution 1 for Formalism.IndefR.Tow.OrbStPf.pd_pds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T09:43:20.347795+00:00
-- url     : https://prove2.me/submissions/90390eb2-1a53-470e-bf4c-2ee5bc35c51d

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_SobolevIteration_DifferentiableUpdate
import Theorems.Thm_Formalism_IndefR_Tow_OrbStPf_pds_nil
import Theorems.Thm_Formalism_IndefR_Tow_OrbStPf_pds_cons
import Theorems.Thm_Formalism_IndefR_Tow_OrbStPf_contDiff_pds
import Theorems.Thm_Formalism_IndefR_Tow_OrbStPf_pd_comm
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
theorem _root_.solution (k : Fin N) (L : List (Fin N)) {f : (Fin N → ℝ) → H} (hf : ContDiff ℝ ∞ f) :
    pd k (pds L f) = pds L (pd k f) := by
  induction L with
  | nil => rfl
  | cons i L ih =>
    simp only [pds_cons]
    rw [pd_comm k i (contDiff_pds L hf), ih]
end Formalism.IndefR.Tow.OrbStPf
