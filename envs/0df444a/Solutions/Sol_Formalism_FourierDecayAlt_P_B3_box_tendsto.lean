-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B3.box_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T16:06:02.712863+00:00
-- url     : https://prove2.me/submissions/40876e57-d3bd-43f2-ace8-7864fe08f742

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AeEqualityFromTestFunctions
import Theorems.Thm_Formalism_FourierDecayAlt_P_B3_pl_nonneg
import Theorems.Thm_Formalism_FourierDecayAlt_P_B3_pl_le_one
import Theorems.Thm_Formalism_FourierDecayAlt_P_B3_pl_contDiff
import Theorems.Thm_Formalism_FourierDecayAlt_P_B3_pl_eventually
import Theorems.Thm_Formalism_FourierDecayAlt_P_B3_pl_prod_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B3_box_fin

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Filter Topology Set
open scoped ENNReal
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B3
open Formalism.FourierDecayAlt.B
namespace Formalism.FourierDecayAlt.P.B3
theorem _root_.solution {f : ℝ × ℝ → ℝ≥0∞} (hf : AEMeasurable f (volume.restrict Quad)) (hfin : FinT f)
    {a₁ a₂ : ℝ} (b₁ b₂ : ℝ) (h₁ : 0 < a₁) (h₂ : 0 < a₂) :
    Tendsto (fun n : ℕ => ∫⁻ τ, ENNReal.ofReal (pl a₁ b₁ n τ.1 * pl a₂ b₂ n τ.2) * f τ ∂(volume.restrict Quad))
      atTop (𝓝 (((volume.restrict Quad).withDensity f) (Ioo a₁ b₁ ×ˢ Ioo a₂ b₂))) := by
  have hS : MeasurableSet (Ioo a₁ b₁ ×ˢ Ioo a₂ b₂) := measurableSet_Ioo.prod measurableSet_Ioo
  rw [withDensity_apply _ hS, ← lintegral_indicator (hs := hS)]
  refine tendsto_lintegral_of_dominated_convergence' ((Ioo a₁ b₁ ×ˢ Ioo a₂ b₂).indicator f)
    (fun n => ?_) (fun n => ?_) ?_ ?_
  · exact (ENNReal.measurable_ofReal.comp
      (((pl_contDiff a₁ b₁ n).continuous.measurable.comp measurable_fst).mul
        ((pl_contDiff a₂ b₂ n).continuous.measurable.comp measurable_snd))).aemeasurable.mul hf
  · refine ae_of_all _ (fun τ => ?_)
    dsimp only
    by_cases hτ : τ ∈ Ioo a₁ b₁ ×ˢ Ioo a₂ b₂
    · rw [Set.indicator_of_mem hτ]
      calc ENNReal.ofReal (pl a₁ b₁ n τ.1 * pl a₂ b₂ n τ.2) * f τ ≤ 1 * f τ := by
            gcongr
            rw [ENNReal.ofReal_le_one]
            nlinarith [pl_le_one a₁ b₁ n τ.1, pl_nonneg a₁ b₁ n τ.1, pl_le_one a₂ b₂ n τ.2, pl_nonneg a₂ b₂ n τ.2]
        _ = f τ := one_mul _
    · rw [pl_prod_zero (Nat.cast_nonneg n) hτ, ENNReal.ofReal_zero, zero_mul]
      simp
  · rw [lintegral_indicator (hs := hS), ← withDensity_apply _ hS]
    exact box_fin hfin b₁ b₂ h₁ h₂
  · refine ae_of_all _ (fun τ => ?_)
    by_cases hτ : τ ∈ Ioo a₁ b₁ ×ˢ Ioo a₂ b₂
    · rw [Set.indicator_of_mem hτ]
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [pl_eventually hτ.1, pl_eventually hτ.2] with n h1 h2
      rw [h1, h2, mul_one, ENNReal.ofReal_one, one_mul]
    · have h0 : (Ioo a₁ b₁ ×ˢ Ioo a₂ b₂).indicator f τ = 0 := by simp [Set.indicator, hτ]
      rw [h0]
      refine tendsto_const_nhds.congr (fun n => ?_)
      rw [pl_prod_zero (Nat.cast_nonneg n) hτ, ENNReal.ofReal_zero, zero_mul]
end Formalism.FourierDecayAlt.P.B3
