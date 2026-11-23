-- Prove2me | solution 1 for Formalism.LT.InverseIntegralClassesKeyFacts.norm_sigma_le_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:38:34.122797+00:00
-- url     : https://prove2.me/submissions/8b10d21c-558d-433b-a3d1-d874a3b90220

import Definitions.Def_Formalism_TorsionNormIteration_InvIntegralOfClass
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_NormSigmaLeOne
import Theorems.Thm_Formalism_LT_InverseIntegralClassesKeyFacts_norm_add_le_of

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
open Formalism Formalism.LT
open Formalism.G
open Formalism.LT.InverseIntegralClassesKeyFacts
variable {K : Type u} [NormedField K] [IsUltrametricDist K]
namespace Formalism.LT.InverseIntegralClassesKeyFacts
theorem _root_.solution {p q : ℕ} {σ : K →+* K} (hσ : IsFrobLift p q σ) (hp1 : ‖(p : K)‖ ≤ 1)
    {a : K} (ha : ‖a‖ ≤ 1) : ‖σ a‖ ≤ 1 := by
  have h1 : ‖σ a - a ^ q‖ ≤ 1 := (hσ a ha).trans hp1
  have h2 : ‖a ^ q‖ ≤ 1 := by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) ha
  have : σ a = (σ a - a ^ q) + a ^ q := by ring
  rw [this]; exact norm_add_le_of h1 h2
end Formalism.LT.InverseIntegralClassesKeyFacts
