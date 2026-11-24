-- Prove2me | solution 1 for Formalism.L2.Th1.E.Main.norm_natCast_of_dvd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T10:37:41.300259+00:00
-- url     : https://prove2.me/submissions/bcaf5e8c-436e-454c-8393-d6e3147b77f0

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_TorsionTranslationPowers_StatementT
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_TorsionTranslationPowers_NonsingularJetNorms_ScaledXOffOrigin

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.E
open Formalism.L2.Th1.E.Main
variable {K : Type} [NormedField K]
namespace Formalism.L2.Th1.E.Main
theorem _root_.solution [IsUltrametricDist K] {n N : ℕ} (h : n ∣ N) (hN : ‖(N : K)‖ = 1) :
    ‖(n : K)‖ = 1 := by
  obtain ⟨d, rfl⟩ := h
  rw [Nat.cast_mul, norm_mul] at hN
  have h1 : ‖(n : K)‖ ≤ 1 := IsUltrametricDist.norm_natCast_le_one K n
  have h2 : ‖(d : K)‖ ≤ 1 := IsUltrametricDist.norm_natCast_le_one K d
  refine le_antisymm h1 ?_
  calc (1 : ℝ) = ‖(n : K)‖ * ‖(d : K)‖ := hN.symm
    _ ≤ ‖(n : K)‖ * 1 := mul_le_mul_of_nonneg_left h2 (norm_nonneg _)
    _ = ‖(n : K)‖ := mul_one _
end Formalism.L2.Th1.E.Main
