-- Prove2me | solution 1 for Eden.derivativeFactors_planar_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:29:22.76292+00:00
-- url     : https://prove2.me/submissions/e9d34f85-2943-427e-893c-873e4b27a159

import Definitions.Def_Eden_VolumeGrowth
import Definitions.Def_Eden_Uniqueness
import Definitions.Def_Eden_VolumeConsequences
import Theorems.Thm_Eden_planarAmplitude_lower_bound
import Theorems.Thm_Eden_radialAmplitude_lower_bound
import Theorems.Thm_P2M_Eden_radiusSq__nonneg_5272e4fb8458
import Theorems.Thm_P2M_Eden_radiusSq__nonneg_7729c3bfdb8d


set_option autoImplicit true
noncomputable section
open Eden
namespace Eden
theorem _root_.solution (c : ℝ) {t : ℝ} (ht : 0 ≤ t)
    {p : PhaseSpace} (hp : p ∈ attractor) (i : Fin 4) :
    Real.exp (-4 * t) ≤ derivativeFactors c t p i.castSucc := by
  have h₂ : Real.exp (-4 * t) ≤ Real.exp (-2 * t) :=
    Real.exp_le_exp.mpr (by linarith)
  fin_cases i
  · exact radialAmplitude_lower_bound ht (radiusSq₁_nonneg p) hp.1
  · exact h₂.trans (planarAmplitude_lower_bound ht (radiusSq₁_nonneg p) hp.1)
  · exact radialAmplitude_lower_bound ht (radiusSq₂_nonneg p) hp.2.1
  · exact h₂.trans (planarAmplitude_lower_bound ht (radiusSq₂_nonneg p) hp.2.1)
end Eden
