-- Prove2me | solution 1 for Formalism.FN.unit_norm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:30:55.021347+00:00
-- url     : https://prove2.me/submissions/31a6cceb-69b4-477a-aeac-3fe0a9a9555b

import Definitions.Def_Formalism_SuccessiveMinima_DefsNP
import Definitions.Def_Formalism_SuccessiveMinima_SuccessiveMinimaProofs_NewtonSlope
import Definitions.Def_Formalism_SuccessiveMinima_SuccessiveMinimaProofs_NPUnit
import Theorems.Thm_Formalism_FN_unit_eps

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FN
open Filter Topology
namespace Formalism.FN
theorem _root_.solution {K : Type} [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K]
    (b : ℕ → K) (r : ℝ) (hr : 0 < r) (hc : ConvOn b r) (hb : b ≠ 0) (hw : wdeg b r = 0)
    (x : K) (hx : ‖x‖ ≤ r) : ‖evalS b x‖ = gNorm b r := by
  obtain ⟨h0, hM, ε, hε0, hε1, hε⟩ := unit_eps b r hr hc hb hw
  have hterm : ∀ k, ‖b k * x ^ k‖ ≤ ‖b k‖ * r ^ k := fun k => by
    rw [norm_mul, norm_pow]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hx k) (norm_nonneg _)
  have hsum : Summable (fun k => b k * x ^ k) := by
    apply NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero
    rw [Nat.cofinite_eq_atTop, tendsto_zero_iff_norm_tendsto_zero]
    exact squeeze_zero (fun k => norm_nonneg _) hterm hc
  have htail : ‖∑' k, b (k + 1) * x ^ (k + 1)‖ ≤ ε * gNorm b r :=
    IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg (by positivity)
      (fun k => (hterm (k + 1)).trans (hε (k + 1) (by omega)))
  have hlt : ε * gNorm b r < gNorm b r := mul_lt_of_lt_one_left hM hε1
  unfold evalS
  rw [hsum.tsum_eq_zero_add, pow_zero, mul_one]
  rw [IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm, h0]
  · exact max_eq_left (htail.trans hlt.le)
  · rw [h0]; exact ne_of_gt (htail.trans_lt hlt)
end Formalism.FN
