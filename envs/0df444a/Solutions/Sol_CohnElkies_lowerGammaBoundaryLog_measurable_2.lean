-- Prove2me | solution 2 for CohnElkies.lowerGammaBoundaryLog_measurable
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:36:44.79201+00:00
-- url     : https://prove2.me/submissions/74d5f846-550d-4f22-b391-a6dafc534884

import Mathlib
import Definitions.Def_SpherePacking
set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped FourierTransform Interval RealInnerProductSpace Topology
theorem h47_measurable_cGamma : Measurable Complex.Gamma := by
  have hseq : ∀ n : ℕ, Measurable (fun s : ℂ => Complex.GammaSeq s n) := by
    intro n
    unfold Complex.GammaSeq
    apply Measurable.div
    · exact (measurable_const.pow measurable_id).mul measurable_const
    · exact Finset.measurable_prod _ (fun j _ => measurable_id.add measurable_const)
  exact measurable_of_tendsto_metrizable hseq
    (tendsto_pi_nhds.mpr fun s => Complex.GammaSeq_tendsto_Gamma s)

theorem solution
    {ℓ : ℝ} (hℓ : 0 < ℓ) (R : ℝ) :
    Measurable (lowerGammaBoundaryLog ℓ R) := by
  unfold lowerGammaBoundaryLog
  have hg := h47_measurable_cGamma
  have h1 : Measurable (fun y : ℝ => -Complex.I * (y : ℂ) / 2) := by fun_prop
  have h2 : Measurable (fun y : ℝ => (ℓ : ℂ) + Complex.I * (y : ℂ) / 2) := by fun_prop
  exact (measurable_const.add (((hg.comp h1).norm).log)).sub ((hg.comp h2).norm.log)

