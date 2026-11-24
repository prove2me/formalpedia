-- Prove2me | solution 1 for Formalism.LT.FrobP.mem_span_of_norm_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T10:33:41.971973+00:00
-- url     : https://prove2.me/submissions/a541e79a-cc5d-4abd-b10d-22cd9cda96e1

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
theorem _root_.solution {p : ℕ} (hp0 : (p : K) ≠ 0) (x : unitBall K)
    (hx : ‖(x : K)‖ ≤ ‖(p : K)‖) : x ∈ Ideal.span {((p : ℕ) : unitBall K)} := by
  have hy : ‖(x : K) / (p : K)‖ ≤ 1 := by
    rw [norm_div]
    first
      | exact div_le_one_of_le₀ hx (norm_nonneg _)
      | exact (div_le_one (norm_pos_iff.mpr hp0)).mpr hx
  refine Ideal.mem_span_singleton'.mpr ⟨⟨(x : K) / (p : K), hy⟩, ?_⟩
  apply Subtype.ext
  show (x : K) / (p : K) * ((p : unitBall K) : K) = (x : K)
  rw [natCast_coe, div_mul_cancel₀ _ hp0]
end Formalism.LT.FrobP
