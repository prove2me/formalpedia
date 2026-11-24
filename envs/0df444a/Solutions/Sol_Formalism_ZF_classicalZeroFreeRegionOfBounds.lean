-- Prove2me | solution 1 for Formalism.ZF.classicalZeroFreeRegionOfBounds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T12:45:17.949865+00:00
-- url     : https://prove2.me/submissions/864d3110-0853-4be2-b8ab-2d911d5a132c

import Definitions.Def_Formalism_ZeroFreeRegion_SmallHeightLogDeriv
import Definitions.Def_Formalism_ZeroFreeRegion_ZetaLogDerivativeBounds_ZfoNegReLeNorm
import Definitions.Def_Formalism_ZeroFreeRegion_ZetaLogDerivativeBounds_ZeroFreeOf
import Theorems.Thm_Formalism_ZF_zfo_large


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex
noncomputable section
open Formalism Formalism.ZF
namespace Formalism.ZF
theorem _root_.solution : ZeroFreeOf := by
  intro h341 hLDR hG hI hSH hLL
  obtain ⟨t₀, -, ht₀⟩ := zfo_large h341 hLDR hG hI hLL
  obtain ⟨c₂, hc₂, hsmall⟩ := hSH t₀
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨min (1 / 200000) (c₂ * Real.log 2), lt_min (by norm_num) (mul_pos hc₂ hlog2), ?_⟩
  intro s hs1 hre
  have hL : Real.log 2 ≤ Real.log (|s.im| + 2) :=
    Real.log_le_log (by norm_num) (by linarith [abs_nonneg s.im])
  have hLpos : 0 < Real.log (|s.im| + 2) := lt_of_lt_of_le hlog2 hL
  rcases le_or_gt |s.im| t₀ with hT | hT
  · apply hsmall s hT _ hs1
    have hc : min (1 / 200000) (c₂ * Real.log 2) / Real.log (|s.im| + 2) ≤ c₂ := by
      rw [div_le_iff₀ hLpos]
      calc min (1 / 200000) (c₂ * Real.log 2) ≤ c₂ * Real.log 2 := min_le_right _ _
        _ ≤ c₂ * Real.log (|s.im| + 2) := mul_le_mul_of_nonneg_left hL hc₂.le
    linarith
  · intro hz
    have hs : s = (s.re : ℂ) + s.im * I := (Complex.re_add_im s).symm
    have hβ := ht₀ s.re s.im hT.le (by rw [← hs]; exact hz)
    have h2 : min (1 / 200000) (c₂ * Real.log 2) / Real.log (|s.im| + 2) ≤ (1 / 200000) / Real.log (|s.im| + 2) :=
      div_le_div_of_nonneg_right (min_le_left _ _) hLpos.le
    linarith
end Formalism.ZF
