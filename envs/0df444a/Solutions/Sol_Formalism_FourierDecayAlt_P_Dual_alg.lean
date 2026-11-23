-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Dual.alg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:31:59.076336+00:00
-- url     : https://prove2.me/submissions/2e4f9565-edc0-4ed6-ba75-c7b6f423d67e

import Definitions.Def_Formalism_HermitianCurvature_StatementL
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DualIdealInclusion

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
theorem _root_.solution {E : Type} [Field E] [NumberField E] (dd : FractionalIdeal (nonZeroDivisors (𝓞 E)) E)
    (hdd : dd ≠ 0) (ν g : ℤ) (hg : g ≠ 0) :
    spanSingleton _ (g : E) * (dd⁻¹ * (dd ^ ν * spanSingleton _ ((g : E) ^ 2))⁻¹) =
      dd ^ (-(ν + 1)) * spanSingleton _ ((g : E)⁻¹) := by
  have hgE : (g : E) ≠ 0 := by exact_mod_cast hg
  rw [mul_inv (dd ^ ν), spanSingleton_inv]
  have h1 : spanSingleton (nonZeroDivisors (𝓞 E)) (g : E) * spanSingleton _ (((g : E) ^ 2)⁻¹) =
      spanSingleton _ ((g : E)⁻¹) := by
    rw [spanSingleton_mul_spanSingleton]; congr 1; field_simp
  rw [show dd ^ (-(ν + 1)) = dd⁻¹ * (dd ^ ν)⁻¹ by
    rw [neg_add, zpow_add₀ hdd, _root_.zpow_neg, zpow_neg_one, mul_comm]]
  rw [← h1]; ring
end Formalism.FourierDecayAlt.P.Dual
