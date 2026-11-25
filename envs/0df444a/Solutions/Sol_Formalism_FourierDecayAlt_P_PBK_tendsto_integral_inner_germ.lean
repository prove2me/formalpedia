-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.PBK.tendsto_integral_inner_germ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T06:14:38.761882+00:00
-- url     : https://prove2.me/submissions/29d43b0d-6f08-4cae-be83-10d83c98fa0d

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BlockPSDCongr
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GermRealisation
import Theorems.Thm_Formalism_FourierDecayAlt_P_PBK_exists_compact_tail

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.PBK
open Formalism.FourierDecayAlt Finset Filter Topology MeasureTheory
open scoped ComplexConjugate InnerProductSpace
noncomputable section
open Classical
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
namespace Formalism.FourierDecayAlt.P.PBK
theorem _root_.solution {α : Type} {l : Filter α} (μ : Measure ℂ) [IsFiniteMeasureOnCompacts μ]
    [NullSingletonClass μ] (F G : α → ℂ → H) (g : ℂ → ℝ) (hg : MemLp g 2 μ) (B : ℝ)
    (hF : ∀ᶠ x in l, MemLp (F x) 2 μ ∧ ∫ D, ‖F x D‖ ^ 2 ∂μ ≤ B)
    (hG : ∀ᶠ x in l, ∀ᵐ D ∂μ, ‖G x D‖ ≤ g D)
    (hloc : ∀ K : Set ℂ, IsCompact K → (0 : ℂ) ∉ K → ∀ δ : ℝ, 0 < δ →
      ∀ᶠ x in l, ∀ᵐ D ∂μ, D ∈ K → ‖F x D‖ ≤ δ) :
    Tendsto (fun x => ∫ D, ⟪F x D, G x D⟫_ℂ ∂μ) l (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hB1p : 0 < max B 0 + 1 := by positivity
  obtain ⟨lam, hlam⟩ : ∃ lam : ℝ, lam = ε / (4 * (max B 0 + 1)) := ⟨_, rfl⟩
  have hlamp : 0 < lam := by rw [hlam]; positivity
  have hg2 : Integrable (fun D => g D ^ 2) μ := (memLp_two_iff_integrable_sq hg.1).1 hg
  obtain ⟨K, hK, h0K, hKt⟩ := exists_compact_tail μ _ hg2 (lam * ε / 2) (by positivity)
  have hKm : MeasurableSet K := hK.isClosed.measurableSet
  have : IsFiniteMeasure (μ.restrict K) := isFiniteMeasure_restrict.mpr hK.measure_lt_top.ne
  have hgK : IntegrableOn (fun D => |g D|) K μ := ((hg.restrict K).integrable one_le_two).abs
  obtain ⟨I, hI⟩ : ∃ I : ℝ, I = ∫ D in K, |g D| ∂μ := ⟨_, rfl⟩
  have hI0 : 0 ≤ I := by rw [hI]; exact setIntegral_nonneg hKm fun D _ => abs_nonneg _
  obtain ⟨δ, hδ⟩ : ∃ δ : ℝ, δ = ε / (4 * (I + 1)) := ⟨_, rfl⟩
  have hδp : 0 < δ := by rw [hδ]; positivity
  filter_upwards [hF, hG, hloc K hK h0K δ hδp] with x hFx hGb hFK
  obtain ⟨hFm, hFB⟩ := hFx
  rw [dist_zero_right]
  have hF2 : Integrable (fun D => ‖F x D‖ ^ 2) μ := (memLp_two_iff_integrable_sq_norm hFm.1).1 hFm
  have i1 : Integrable (fun D => δ * K.indicator (fun D => |g D|) D) μ :=
    (hgK.integrable_indicator hKm).const_mul δ
  have i2 : Integrable (fun D => lam * ‖F x D‖ ^ 2) μ := hF2.const_mul lam
  have i3 : Integrable (fun D => Kᶜ.indicator (fun D => g D ^ 2) D / lam) μ :=
    (hg2.indicator hKm.compl).div_const lam
  have i4 : Integrable (fun D => (lam * ‖F x D‖ ^ 2 + Kᶜ.indicator (fun D => g D ^ 2) D / lam) / 2) μ :=
    (i2.add i3).div_const 2
  have hpt : ∀ᵐ D ∂μ, ‖⟪F x D, G x D⟫_ℂ‖ ≤ δ * K.indicator (fun D => |g D|) D +
      (lam * ‖F x D‖ ^ 2 + Kᶜ.indicator (fun D => g D ^ 2) D / lam) / 2 := by
    filter_upwards [hGb, hFK] with D hb hk
    have h1 : ‖⟪F x D, G x D⟫_ℂ‖ ≤ ‖F x D‖ * g D :=
      (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left hb (norm_nonneg _))
    have hg0 : 0 ≤ g D := (norm_nonneg _).trans hb
    by_cases hDK : D ∈ K
    · have hFD := hk hDK
      rw [Set.indicator_of_mem hDK, Set.indicator_of_notMem (Set.notMem_compl_iff.mpr hDK), abs_of_nonneg hg0]
      have : ‖F x D‖ * g D ≤ δ * g D := mul_le_mul_of_nonneg_right hFD hg0
      have : 0 ≤ lam * ‖F x D‖ ^ 2 := by positivity
      have : (lam * ‖F x D‖ ^ 2 + 0 / lam) / 2 ≥ 0 := by rw [zero_div, add_zero]; positivity
      linarith
    · rw [Set.indicator_of_notMem hDK, Set.indicator_of_mem (Set.mem_compl hDK)]
      have key : lam * ‖F x D‖ ^ 2 + g D ^ 2 / lam - 2 * (‖F x D‖ * g D) = (lam * ‖F x D‖ - g D) ^ 2 / lam := by
        field_simp
        ring
      have : 0 ≤ (lam * ‖F x D‖ - g D) ^ 2 / lam := by positivity
      have : δ * 0 = 0 := mul_zero δ
      linarith
  have hInt : ∫ D, (δ * K.indicator (fun D => |g D|) D +
      (lam * ‖F x D‖ ^ 2 + Kᶜ.indicator (fun D => g D ^ 2) D / lam) / 2) ∂μ =
      δ * I + (lam * ∫ D, ‖F x D‖ ^ 2 ∂μ + (∫ D in Kᶜ, g D ^ 2 ∂μ) / lam) / 2 := by
    rw [integral_add i1 i4, integral_const_mul, integral_indicator hKm, integral_div, integral_add i2 i3,
      integral_const_mul, integral_div, integral_indicator hKm.compl, hI]
  have e1 : δ * I ≤ ε / 4 := by
    rw [hδ, div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  have e2 : lam * ∫ D, ‖F x D‖ ^ 2 ∂μ ≤ ε / 4 := by
    have hle : ∫ D, ‖F x D‖ ^ 2 ∂μ ≤ max B 0 + 1 := by linarith [le_max_left B 0]
    calc lam * ∫ D, ‖F x D‖ ^ 2 ∂μ ≤ lam * (max B 0 + 1) := mul_le_mul_of_nonneg_left hle hlamp.le
      _ = ε / 4 := by rw [hlam]; field_simp
  have e3 : (∫ D in Kᶜ, g D ^ 2 ∂μ) / lam < ε / 2 := by
    rw [div_lt_iff₀ hlamp]
    linarith
  calc ‖∫ D, ⟪F x D, G x D⟫_ℂ ∂μ‖ ≤ ∫ D, ‖⟪F x D, G x D⟫_ℂ‖ ∂μ := norm_integral_le_integral_norm _
    _ ≤ ∫ D, (δ * K.indicator (fun D => |g D|) D +
        (lam * ‖F x D‖ ^ 2 + Kᶜ.indicator (fun D => g D ^ 2) D / lam) / 2) ∂μ :=
      integral_mono_of_nonneg (Eventually.of_forall fun _ => norm_nonneg _) (i1.add i4) hpt
    _ = _ := hInt
    _ < ε := by linarith
end Formalism.FourierDecayAlt.P.PBK
