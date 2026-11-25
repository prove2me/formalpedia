-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.PBK.tendsto_inner_dil
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T06:59:58.725595+00:00
-- url     : https://prove2.me/submissions/abe6a50a-1cf2-419d-9c1d-907b52a945f0

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RootPushforwardDensity
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LastBlockDecay
import Theorems.Thm_Formalism_FourierDecayAlt_P_PBK_memLp_dil
import Theorems.Thm_Formalism_FourierDecayAlt_P_PBK_tendsto_dil

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.PBK
open MeasureTheory Filter Topology
open scoped InnerProductSpace
noncomputable section
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
namespace Formalism.FourierDecayAlt.P.PBK
theorem _root_.solution {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (b c : ℂ → H)
    (hb : MemLp b 2 volume) (hc : MemLp c 2 volume) (ζ : ℂ) (hζ : ζ ≠ 0) :
    Tendsto (fun ρ : ℂ => ∫ z, ‖⟪b z, ((‖ρ‖ : ℝ) : ℂ) • c (ρ * z)⟫_ℂ - ⟪b z, ((‖ζ‖ : ℝ) : ℂ) • c (ζ * z)⟫_ℂ‖)
      (𝓝 ζ) (𝓝 0) := by
  have hT := tendsto_dil c hc ζ hζ
  set K : ℝ := (∫ z, ‖b z‖ ^ (2 : ℝ)) ^ (1 / (2 : ℝ))
  have hG : Tendsto (fun ρ : ℂ => K * (∫ z, ‖‖ρ‖ • c (ρ * z) - ‖ζ‖ • c (ζ * z)‖ ^ 2) ^ (1 / (2 : ℝ)))
      (𝓝 ζ) (𝓝 0) := by
    have h1 := ((Real.continuous_rpow_const (by norm_num : (0 : ℝ) ≤ 1 / 2)).tendsto 0).comp hT
    rw [Real.zero_rpow (by norm_num)] at h1
    simpa using h1.const_mul K
  refine squeeze_zero' (Filter.Eventually.of_forall fun ρ => integral_nonneg fun _ => norm_nonneg _) ?_ hG
  filter_upwards [eventually_ne_nhds hζ] with ρ hρ0
  have hb2 : MemLp b (ENNReal.ofReal 2) volume := by simpa using hb
  have hd : MemLp (fun z => ‖ρ‖ • c (ρ * z) - ‖ζ‖ • c (ζ * z)) 2 volume :=
    (memLp_dil hc ρ hρ0).sub (memLp_dil hc ζ hζ)
  have hd2 : MemLp (fun z => ‖ρ‖ • c (ρ * z) - ‖ζ‖ • c (ζ * z)) (ENNReal.ofReal 2) volume := by
    simpa using hd
  have hint : Integrable (fun z => ‖b z‖ * ‖‖ρ‖ • c (ρ * z) - ‖ζ‖ • c (ζ * z)‖) volume :=
    hb.norm.integrable_mul hd.norm
  have hpt : ∀ z, ‖⟪b z, ((‖ρ‖ : ℝ) : ℂ) • c (ρ * z)⟫_ℂ - ⟪b z, ((‖ζ‖ : ℝ) : ℂ) • c (ζ * z)⟫_ℂ‖ ≤
      ‖b z‖ * ‖‖ρ‖ • c (ρ * z) - ‖ζ‖ • c (ζ * z)‖ := by
    intro z
    rw [← inner_sub_right, Complex.coe_smul, Complex.coe_smul]
    exact norm_inner_le_norm _ _
  calc ∫ z, ‖⟪b z, ((‖ρ‖ : ℝ) : ℂ) • c (ρ * z)⟫_ℂ - ⟪b z, ((‖ζ‖ : ℝ) : ℂ) • c (ζ * z)⟫_ℂ‖
      ≤ ∫ z, ‖b z‖ * ‖‖ρ‖ • c (ρ * z) - ‖ζ‖ • c (ζ * z)‖ :=
        integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => norm_nonneg _) hint
          (Filter.Eventually.of_forall hpt)
    _ ≤ K * (∫ z, ‖‖ρ‖ • c (ρ * z) - ‖ζ‖ • c (ζ * z)‖ ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) :=
        integral_mul_norm_le_Lp_mul_Lq Real.HolderConjugate.two_two hb2 hd2
    _ = K * (∫ z, ‖‖ρ‖ • c (ρ * z) - ‖ζ‖ • c (ζ * z)‖ ^ 2) ^ (1 / (2 : ℝ)) := by
        congr 2
        congr 1
        funext z
        exact Real.rpow_two _
end Formalism.FourierDecayAlt.P.PBK
