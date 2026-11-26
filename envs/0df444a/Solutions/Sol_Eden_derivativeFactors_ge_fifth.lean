-- Prove2me | solution 1 for Eden.derivativeFactors_ge_fifth
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:38:59.448199+00:00
-- url     : https://prove2.me/submissions/2d2a9198-257d-4536-bc8e-184af5a3e2ca

import Definitions.Def_Eden_InvariantSets
import Definitions.Def_Eden_GrowthRates
import Definitions.Def_Eden_SingularValues
import Definitions.Def_Eden_FactorBounds
import Theorems.Thm_Eden_radialAmplitude_lower_bound
import Theorems.Thm_Eden_planarAmplitude_lower_bound
import Theorems.Thm_P2M_Eden_radiusSq__nonneg_5272e4fb8458
import Theorems.Thm_P2M_Eden_radiusSq__nonneg_7729c3bfdb8d


set_option autoImplicit true
noncomputable section
open Set
open Eden
namespace Eden
theorem _root_.solution {c t : ℝ} (hc : 4 ≤ c) (ht : 0 ≤ t)
    {p : PhaseSpace} (hp : p ∈ attractor) (i : Fin 5) :
    Real.exp (-c * t) ≤ derivativeFactors c t p i := by
  have h₄ : Real.exp (-c * t) ≤ Real.exp (-4 * t) :=
    Real.exp_le_exp.mpr (by nlinarith)
  have h₂ : Real.exp (-c * t) ≤ Real.exp (-2 * t) :=
    Real.exp_le_exp.mpr (by nlinarith)
  fin_cases i
  · exact h₄.trans (radialAmplitude_lower_bound ht (radiusSq₁_nonneg p) hp.1)
  · exact h₂.trans (planarAmplitude_lower_bound ht (radiusSq₁_nonneg p) hp.1)
  · exact h₄.trans (radialAmplitude_lower_bound ht (radiusSq₂_nonneg p) hp.2.1)
  · exact h₂.trans (planarAmplitude_lower_bound ht (radiusSq₂_nonneg p) hp.2.1)
  · exact le_rfl
end Eden
