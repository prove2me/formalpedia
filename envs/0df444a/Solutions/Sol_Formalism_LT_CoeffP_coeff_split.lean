-- Prove2me | solution 1 for Formalism.LT.CoeffP.coeff_split
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T10:32:06.133186+00:00
-- url     : https://prove2.me/submissions/6c861448-85b4-4563-af04-33a0b60504f8

import Definitions.Def_Formalism_TorsionNormIteration_InvIntegralOfClass
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_SigmaNormLeOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PowerSeries
universe u v
open Formalism Formalism.LT Formalism.LT.CoeffP
open Formalism.G
variable {K : Type u} [NormedField K] [IsUltrametricDist K]
namespace Formalism.LT.CoeffP
theorem _root_.solution (p q : ℕ) (hq : q ≠ 0) (σ : K →+* K) (f : PowerSeries K) (n : ℕ) :
    coeff n f = coeff n (f - (p : K)⁻¹ • (PowerSeries.map σ f).subst
        ((PowerSeries.X : PowerSeries K) ^ q)) +
      (p : K)⁻¹ * (if q ∣ n then σ (coeff (n / q) f) else 0) := by
  rw [map_sub, map_smul, PowerSeries.coeff_subst_X_pow hq, PowerSeries.coeff_map, smul_eq_mul]
  split_ifs <;> simp
end Formalism.LT.CoeffP
