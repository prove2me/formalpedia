-- Prove2me | solution 1 for Formalism.LT.FrobP.natCast_nonunit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T10:33:44.290305+00:00
-- url     : https://prove2.me/submissions/32b62f25-1492-4fcc-a1e9-3183777fd046

import Definitions.Def_Formalism_TorsionNormIteration_InvIntegralOfClass
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_MemSpanOfNormLe
import Theorems.Thm_Formalism_LT_FrobP_natCast_coe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
universe u v
open Formalism Formalism.LT Formalism.LT.FrobP
open Formalism.G
variable {K : Type u} [NormedField K] [IsUltrametricDist K]
namespace Formalism.LT.FrobP
theorem _root_.solution {p : ℕ} (hp : ‖(p : K)‖ < 1) :
    ((p : ℕ) : unitBall K) ∈ nonunits (unitBall K) := by
  rw [mem_nonunits_iff]
  intro hu
  obtain ⟨u, hu'⟩ := hu.exists_left_inv
  have h2 : (u : K) * (p : K) = 1 := by
    have h0 := congrArg Subtype.val hu'
    rw [← natCast_coe p]
    exact h0
  have hu1 : ‖(u : K)‖ ≤ 1 := u.2
  have h3 := congrArg norm h2
  rw [norm_mul, norm_one] at h3
  have h4 : ‖(u : K)‖ * ‖(p : K)‖ ≤ ‖(p : K)‖ := by
    calc ‖(u : K)‖ * ‖(p : K)‖ ≤ 1 * ‖(p : K)‖ := mul_le_mul_of_nonneg_right hu1 (norm_nonneg _)
      _ = ‖(p : K)‖ := one_mul _
  linarith
end Formalism.LT.FrobP
