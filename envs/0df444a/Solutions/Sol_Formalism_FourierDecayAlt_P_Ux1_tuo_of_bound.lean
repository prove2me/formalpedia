-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Ux1.tuo_of_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T18:14:05.442794+00:00
-- url     : https://prove2.me/submissions/6e895837-75d5-41f6-8fa2-15ca5da0235f

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_CayleyForm
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CompactlySupportedBanachModel

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Ux1
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.B4
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace Formalism.FourierDecayAlt.P.Ux1
theorem _root_.solution {α F : Type*} [NormedAddCommGroup F] {G : ℕ → α → F} {f : α → F} {s : Set α} {B : ℝ}
    {ε : ℕ → ℝ} (hε : Tendsto ε atTop (𝓝 0)) (h : ∀ n, ∀ x ∈ s, ‖G n x - f x‖ ≤ B * ε n) :
    TendstoUniformlyOn G f atTop s := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro δ hδ
  have hB : 0 < |B| + 1 := by positivity
  have hev := Metric.tendsto_nhds.1 hε (δ / (|B| + 1)) (by positivity)
  filter_upwards [hev] with n hn x hx
  rw [Real.dist_eq, sub_zero] at hn
  rw [dist_eq_norm, norm_sub_rev]
  calc ‖G n x - f x‖ ≤ B * ε n := h n x hx
    _ ≤ |B * ε n| := le_abs_self _
    _ = |B| * |ε n| := abs_mul _ _
    _ ≤ |B| * (δ / (|B| + 1)) := mul_le_mul_of_nonneg_left hn.le (abs_nonneg _)
    _ < δ := by
        rw [mul_div_assoc', div_lt_iff₀ hB]; nlinarith [abs_nonneg B]
end Formalism.FourierDecayAlt.P.Ux1
