-- Prove2me | solution 1 for Formalism.LT.CoeffP.sigma_norm_le_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T10:33:43.727469+00:00
-- url     : https://prove2.me/submissions/871e09fb-bfb8-442f-a200-f6189ae0f594

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
theorem _root_.solution {p q : ℕ} {σ : K →+* K} (hp : ‖(p : K)‖ ≤ 1)
    (hσ : IsFrobLift p q σ) (a : K) (ha : ‖a‖ ≤ 1) : ‖σ a‖ ≤ 1 := by
  have h1 : ‖σ a - a ^ q‖ ≤ ‖(p : K)‖ := hσ a ha
  have h2 : ‖a ^ q‖ ≤ 1 := by
    rw [norm_pow]
    simpa using pow_le_pow_of_le_one (norm_nonneg a) ha (Nat.zero_le q)
  calc ‖σ a‖ = ‖(σ a - a ^ q) + a ^ q‖ := by rw [sub_add_cancel]
    _ ≤ max ‖σ a - a ^ q‖ ‖a ^ q‖ := IsUltrametricDist.norm_add_le_max _ _
    _ ≤ 1 := max_le (h1.trans hp) h2
end Formalism.LT.CoeffP
