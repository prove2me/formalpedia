-- Prove2me | solution 1 for Formalism.IndefR.Tow.OrbStPf.pd_comm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:07:21.902378+00:00
-- url     : https://prove2.me/submissions/1c7c6f00-78cb-4773-a594-89d36fe311a7

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
section
noncomputable section
open scoped ContDiff
namespace Formalism.IndefR.Tow.OrbStPf
variable {N : ℕ} {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
private lemma fderiv_apply_lemma (g : (Fin N → ℝ) → ((Fin N → ℝ) →L[ℝ] H)) (v w p : Fin N → ℝ)
    (hg : DifferentiableAt ℝ g p) : fderiv ℝ (fun q => g q v) p w = fderiv ℝ g p w v := by
  rw [fderiv_clm_apply hg (differentiableAt_const v)]
  simp
end Formalism.IndefR.Tow.OrbStPf
end
end

set_option autoImplicit false
noncomputable section
open scoped ContDiff
open Formalism Formalism.IndefR Formalism.IndefR.Tow Formalism.IndefR.Tow.OrbStPf
variable {N : ℕ} {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
namespace Formalism.IndefR.Tow.OrbStPf
theorem _root_.solution (i j : Fin N) {f : (Fin N → ℝ) → H} (hf : ContDiff ℝ ∞ f) :
    pd i (pd j f) = pd j (pd i f) := by
  have hd : ContDiff ℝ ∞ (fderiv ℝ f) := hf.fderiv_right (m := ∞) (by simp)
  funext p
  have hs := (hf.contDiffAt (x := p)).isSymmSndFDerivAt
    (by simp <;> first | exact WithTop.coe_le_coe.2 le_top | norm_cast | decide | exact le_top)
  show fderiv ℝ (fun q => fderiv ℝ f q (Pi.single j 1)) p (Pi.single i 1) =
    fderiv ℝ (fun q => fderiv ℝ f q (Pi.single i 1)) p (Pi.single j 1)
  rw [fderiv_apply_lemma _ _ _ _ (hd.differentiable (by simp) p),
    fderiv_apply_lemma _ _ _ _ (hd.differentiable (by simp) p)]
  exact hs _ _
end Formalism.IndefR.Tow.OrbStPf
