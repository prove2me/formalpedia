-- Prove2me | solution 1 for CohnElkies.stripPoissonCoreMass_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:34.337066+00:00
-- url     : https://prove2.me/submissions/df6ac1af-a465-42e7-97d1-4b87ef0058ea

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_stripPoissonKernel_pos
import Theorems.Thm_CohnElkies_stripPoissonKernel_integrable
import Theorems.Thm_CohnElkies_stripPoissonKernel_antitone_abs

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Metric Set
open scoped ENNReal Interval Topology
namespace CohnElkies
theorem _root_.solution
    {σ : ℝ} (hbelow : -1 < σ) (habove : σ < 1) :
    0 < stripPoissonCoreMass σ := by
  have hk := stripPoissonKernel_integrable hbelow habove
  have hkone := stripPoissonKernel_pos hbelow habove 1
  have hconstant : IntegrableOn
      (fun _T : ℝ => stripPoissonKernel σ 1)
      (Icc (-1 : ℝ) 1) :=
    (continuous_const : Continuous
      (fun _T : ℝ => stripPoissonKernel σ 1)).integrableOn_Icc
  have hcompare :
      (∫ _T in Icc (-1 : ℝ) 1,
        stripPoissonKernel σ 1) ≤
        ∫ T in Icc (-1 : ℝ) 1,
          stripPoissonKernel σ T := by
    apply setIntegral_mono_on hconstant hk.integrableOn
      measurableSet_Icc
    intro T hT
    apply stripPoissonKernel_antitone_abs
      hbelow habove
    rw [abs_of_pos (by norm_num : (0 : ℝ) < 1)]
    exact (abs_le).mpr hT
  have hvalue :
      (∫ _T in Icc (-1 : ℝ) 1,
        stripPoissonKernel σ 1) =
        2 * stripPoissonKernel σ 1 := by
    norm_num
  rw [hvalue] at hcompare
  unfold stripPoissonCoreMass
  nlinarith
end CohnElkies
