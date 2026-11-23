-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Dual.dual_third_group_integral
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:55:55.17262+00:00
-- url     : https://prove2.me/submissions/dd5e8c8b-2b32-42dc-9063-ad767bb924a3

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
theorem _root_.solution : Formalism.FourierDecayAlt.L.DualLatticeInclusion := by
  intro E _ _ dd h1 ν g hg La hLa x hx
  have hdd : dd ≠ 0 := by
    intro h0; rw [h0, _root_.inv_zero] at h1; exact dual_ne_zero ℤ ℚ (one_ne_zero (α := FractionalIdeal (nonZeroDivisors (𝓞 E)) E)) h1
  have hgE : (g : E) ≠ 0 := by exact_mod_cast hg
  have hJ : dd ^ ν * spanSingleton (nonZeroDivisors (𝓞 E)) ((g : E) ^ 2) ≠ 0 :=
    mul_ne_zero (zpow_ne_zero _ hdd) (by simp [spanSingleton_eq_zero_iff, hgE])
  have hy : x * (g : E)⁻¹ ∈ dual ℤ ℚ (dd ^ ν * spanSingleton _ ((g : E) ^ 2)) := by
    rw [mem_dual hJ]
    intro a ha
    have := hx a (hLa a ha)
    rw [Algebra.traceForm_apply]
    convert this using 2
    field_simp
  rw [dual_eq_mul_inv ℤ ℚ, h1] at hy
  rw [← alg dd hdd ν g hg]
  have := mul_mem_mul (mem_spanSingleton_self (nonZeroDivisors (𝓞 E)) (g : E)) hy
  convert this using 1
  field_simp
end Formalism.FourierDecayAlt.P.Dual
