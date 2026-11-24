-- Prove2me | solution 1 for Formalism.ZF.MoebiusInverseZetaBounds.rpow_le_integral
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T11:42:16.899069+00:00
-- url     : https://prove2.me/submissions/27a80aef-c121-4113-8a28-2554b71f37cb

import Definitions.Def_Formalism_ZeroFreeRegion_SmallHeightLogDeriv
import Definitions.Def_Formalism_ZeroFreeRegion_ZetaLogDerivativeBounds_ZetaInvBound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Filter Topology LSeries ArithmeticFunction
noncomputable section
open Formalism Formalism.ZF
open Formalism.ZF.MoebiusInverseZetaBounds
namespace Formalism.ZF.MoebiusInverseZetaBounds
theorem _root_.solution {x σ : ℝ} (hx : 0 < x) (hσ : 0 < σ) :
    (x + 1) ^ (-σ - 1) ≤ (x ^ (-σ) - (x + 1) ^ (-σ)) / σ := by
  have ha : 0 < x + 1 := by linarith
  have hy : 0 < x / (x + 1) := div_pos hx ha
  have hlog : Real.log (x / (x + 1)) ≤ x / (x + 1) - 1 := Real.log_le_sub_one_of_pos hy
  have hexp : 1 + σ / (x + 1) ≤ (x / (x + 1)) ^ (-σ) := by
    rw [Real.rpow_def_of_pos hy]
    have h1 := Real.add_one_le_exp (Real.log (x / (x + 1)) * (-σ))
    have h2 : σ / (x + 1) ≤ Real.log (x / (x + 1)) * (-σ) := by
      have e : σ / (x + 1) = (x / (x + 1) - 1) * (-σ) := by
        field_simp
        ring
      rw [e]
      exact mul_le_mul_of_nonpos_right hlog (by linarith)
    linarith
  have hA := Real.rpow_pos_of_pos ha (-σ)
  have hsplit : x ^ (-σ) = (x + 1) ^ (-σ) * (x / (x + 1)) ^ (-σ) := by
    rw [Real.div_rpow hx.le ha.le]
    field_simp
  have hm1 : (x + 1) ^ (-σ - 1) = (x + 1) ^ (-σ) / (x + 1) := by
    rw [Real.rpow_sub ha, Real.rpow_one]
  rw [le_div_iff₀ hσ, hm1, hsplit]
  have hmul : (x + 1) ^ (-σ) * (σ / (x + 1)) ≤ (x + 1) ^ (-σ) * ((x / (x + 1)) ^ (-σ) - 1) :=
    mul_le_mul_of_nonneg_left (by linarith) hA.le
  calc (x + 1) ^ (-σ) / (x + 1) * σ = (x + 1) ^ (-σ) * (σ / (x + 1)) := by ring
    _ ≤ (x + 1) ^ (-σ) * ((x / (x + 1)) ^ (-σ) - 1) := hmul
    _ = (x + 1) ^ (-σ) * (x / (x + 1)) ^ (-σ) - (x + 1) ^ (-σ) := by ring
end Formalism.ZF.MoebiusInverseZetaBounds
