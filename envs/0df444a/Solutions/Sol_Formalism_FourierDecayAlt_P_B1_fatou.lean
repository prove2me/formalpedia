-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B1.fatou
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T14:32:09.725299+00:00
-- url     : https://prove2.me/submissions/cfb54067-c4d7-470d-a243-11d20e5f6b79

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralZeroFrequencyInvariant

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B1
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B
namespace Formalism.FourierDecayAlt.P.B1
theorem _root_.solution : FatouParam := by
  intro Q _ μ E _ U J c hU hJm hJc hc hae τ hτ
  have hNe : (ae (volume.restrict U) ⊓ 𝓝 τ).NeBot := by
    rw [Filter.inf_neBot_iff]
    intro s₁ hs₁ s₂ hs₂
    by_contra hemp
    rw [Set.not_nonempty_iff_eq_empty] at hemp
    have hO : τ ∈ interior (s₂ ∩ U) :=
      mem_interior_iff_mem_nhds.mpr (Filter.inter_mem hs₂ (hU.mem_nhds hτ))
    have hpos : 0 < volume (interior (s₂ ∩ U)) := isOpen_interior.measure_pos volume ⟨τ, hO⟩
    have hsub : interior (s₂ ∩ U) ⊆ s₁ᶜ := by
      intro t ht hts
      have hmem : t ∈ s₁ ∩ s₂ := ⟨hts, (interior_subset ht).1⟩
      rw [hemp] at hmem
      exact hmem
    have h0' : volume.restrict U s₁ᶜ = 0 := mem_ae_iff.mp hs₁
    have hle2 : volume.restrict U (interior (s₂ ∩ U)) ≤ volume.restrict U s₁ᶜ := measure_mono hsub
    rw [h0', Measure.restrict_apply isOpen_interior.measurableSet,
      Set.inter_eq_left.mpr (interior_subset.trans Set.inter_subset_right)] at hle2
    exact lt_irrefl _ (hpos.trans_le hle2)
  have hex : ∀ n : ℕ, ∃ σ, σ ∈ Metric.ball τ (1 / ((n : ℝ) + 1)) ∩ U ∧
      ∫⁻ q, ‖J σ q‖ₑ ^ 2 ∂μ = ENNReal.ofReal (c σ) := by
    intro n
    have h1 : Metric.ball τ (1 / ((n : ℝ) + 1)) ∩ U ∈ 𝓝 τ :=
      Filter.inter_mem (Metric.ball_mem_nhds τ (by positivity)) (hU.mem_nhds hτ)
    obtain ⟨σ, hσ1, hσ2⟩ := Filter.inf_neBot_iff.mp hNe hae h1
    exact ⟨σ, hσ2, hσ1⟩
  choose σ hσ hσeq using hex
  have hσT : Tendsto σ atTop (𝓝 τ) := by
    rw [tendsto_iff_dist_tendsto_zero]
    refine squeeze_zero (fun n => dist_nonneg) (fun n => ?_) tendsto_one_div_add_atTop_nhds_zero_nat
    exact (Metric.mem_ball.mp (hσ n).1).le
  have hσW : Tendsto σ atTop (𝓝[U] τ) :=
    tendsto_nhdsWithin_iff.mpr ⟨hσT, Filter.Eventually.of_forall fun n => (hσ n).2⟩
  have hpt : ∀ᵐ q ∂μ, Tendsto (fun n => ‖J (σ n) q‖ₑ ^ 2) atTop (𝓝 (‖J τ q‖ₑ ^ 2)) := by
    filter_upwards [hJc] with q hq
    have h2 := ((hq τ hτ).tendsto).comp hσW
    exact ((ENNReal.continuous_pow 2).tendsto _).comp ((continuous_enorm.tendsto _).comp h2)
  have hcT : Tendsto (fun n => ENNReal.ofReal (c (σ n))) atTop (𝓝 (ENNReal.ofReal (c τ))) :=
    (ENNReal.continuous_ofReal.tendsto _).comp ((hc τ hτ).tendsto.comp hσW)
  calc ∫⁻ q, ‖J τ q‖ₑ ^ 2 ∂μ = ∫⁻ q, liminf (fun n => ‖J (σ n) q‖ₑ ^ 2) atTop ∂μ := by
        apply lintegral_congr_ae
        filter_upwards [hpt] with q hq
        exact hq.liminf_eq.symm
    _ ≤ liminf (fun n => ∫⁻ q, ‖J (σ n) q‖ₑ ^ 2 ∂μ) atTop := by
        apply lintegral_liminf_le'
        intro n
        exact ((hJm (σ n) (hσ n).2).enorm).pow_const 2
    _ = liminf (fun n => ENNReal.ofReal (c (σ n))) atTop := by
        simp only [hσeq]
    _ = ENNReal.ofReal (c τ) := hcT.liminf_eq
end Formalism.FourierDecayAlt.P.B1
