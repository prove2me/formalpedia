-- Prove2me | solution 1 for Formalism.IndefR.Tow.OrbStPf.pds_update
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T09:49:17.149313+00:00
-- url     : https://prove2.me/submissions/cda26f4f-49d5-4875-9be6-afd811837584

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_SobolevIteration_DifferentiableUpdate
import Theorems.Thm_Formalism_IndefR_Tow_OrbStPf_pds_nil
import Theorems.Thm_Formalism_IndefR_Tow_OrbStPf_pds_cons
import Theorems.Thm_Formalism_IndefR_Tow_OrbStPf_differentiable_pds
import Theorems.Thm_Formalism_IndefR_Tow_OrbStPf_pd_update
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
theorem _root_.solution (L : List (Fin N)) (j : Fin N) (hL : ∀ i ∈ L, i ≠ j) (s : ℝ) {g : (Fin N → ℝ) → H}
    (hg : ContDiff ℝ ∞ g) :
    pds L (fun r => g (Function.update r j s)) = fun r => pds L g (Function.update r j s) := by
  induction L with
  | nil => rfl
  | cons i L ih =>
    simp only [pds_cons]
    rw [ih (fun k hk => hL k (by simp [hk])),
      pd_update i j (hL i (by simp)) s (differentiable_pds L hg)]
end Formalism.IndefR.Tow.OrbStPf
