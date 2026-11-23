-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Dual.dual_ideal_inclusion
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:55:55.319983+00:00
-- url     : https://prove2.me/submissions/0a3e270a-9cb1-402e-975d-8acbe4762fca

import Definitions.Def_Formalism_HermitianCurvature_StatementL
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DualIdealInclusion
import Theorems.Thm_Formalism_FourierDecayAlt_P_Dual_alg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Dual
open NumberField FractionalIdeal
namespace Formalism.FourierDecayAlt.P.Dual
theorem _root_.solution : Formalism.FourierDecayAlt.L.DualIdealInclusion := by
  intro E _ _ dd h1 ν g hg La hLa
  have hdd : dd ≠ 0 := by
    intro h0; rw [h0, _root_.inv_zero] at h1; exact dual_ne_zero ℤ ℚ (one_ne_zero (α := FractionalIdeal (nonZeroDivisors (𝓞 E)) E)) h1
  have hgE : (g : E) ≠ 0 := by exact_mod_cast hg
  have hJ : dd ^ ν * spanSingleton (nonZeroDivisors (𝓞 E)) ((g : E) ^ 2) ≠ 0 :=
    mul_ne_zero (zpow_ne_zero _ hdd) (by simp [spanSingleton_eq_zero_iff, hgE])
  have hLa0 : La ≠ 0 := fun h => hJ (le_antisymm (by simpa [h] using hLa) (FractionalIdeal.zero_le _))
  have hd := (dual_le_dual ℤ ℚ hLa0 hJ).mpr hLa
  rw [dual_eq_mul_inv ℤ ℚ (dd ^ ν * spanSingleton _ ((g : E) ^ 2)), h1] at hd
  calc spanSingleton _ (g : E) * dual ℤ ℚ La
      ≤ spanSingleton _ (g : E) * (dd⁻¹ * (dd ^ ν * spanSingleton _ ((g : E) ^ 2))⁻¹) :=
        mul_le_mul_right hd _
    _ = _ := alg dd hdd ν g hg
end Formalism.FourierDecayAlt.P.Dual
