-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.PBK.tendsto_integral_inner_germ_moving
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T07:00:02.047788+00:00
-- url     : https://prove2.me/submissions/881c1740-f27b-4e8a-a686-56900cff7f4e

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GermFibreKernels
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TendstoIntegralInnerGermMoving
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace Formalism.FourierDecayAlt.P.PBK
open Formalism.FourierDecayAlt Finset Filter Topology MeasureTheory
open scoped ComplexConjugate InnerProductSpace
noncomputable section
section L2m
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
private lemma mul_le_young_bounds_of_le_add {nF nG g e t δ : ℝ} (ht : 0 < t) (hδ : 0 ≤ δ) (hnF : 0 ≤ nF)
    (hG : nG ≤ g + e) :
    (nF ≤ δ → nF * nG ≤ t * nF ^ 2 + (0 + e ^ 2) / (2 * t) + δ / 2 * (1 + g ^ 2)) ∧
      nF * nG ≤ t * nF ^ 2 + (g ^ 2 + e ^ 2) / (2 * t) + δ / 2 * (0 + g ^ 2) := by
  have h2t : 0 < 2 * t := by positivity
  have hGa : nF * nG ≤ nF * |g| + nF * |e| := by
    have : nG ≤ |g| + |e| := hG.trans (add_le_add (le_abs_self g) (le_abs_self e))
    nlinarith

  have hA : ∀ y : ℝ, nF * |y| ≤ t * nF ^ 2 / 2 + y ^ 2 / (2 * t) := by
    intro y
    rw [show t * nF ^ 2 / 2 + y ^ 2 / (2 * t) = (t ^ 2 * nF ^ 2 + y ^ 2) / (2 * t) by field_simp <;> ring,
      le_div_iff₀ h2t]
    nlinarith [sq_nonneg (t * nF - |y|), sq_abs y]
  have hg1 : |g| ≤ (1 + g ^ 2) / 2 := by nlinarith [sq_nonneg (|g| - 1), sq_abs g]
  refine ⟨fun hK => ?_, ?_⟩
  · have h1 : nF * |g| ≤ δ * |g| := mul_le_mul_of_nonneg_right hK (abs_nonneg g)
    have h2 : δ * |g| ≤ δ / 2 * (1 + g ^ 2) := by nlinarith
    have h3 := hA e
    have h4 : t * nF ^ 2 / 2 ≤ t * nF ^ 2 := by nlinarith [sq_nonneg nF]
    have h5 : (0 + e ^ 2) / (2 * t) = e ^ 2 / (2 * t) := by ring
    rw [h5]
    linarith
  · have h3 := hA e
    have h4 := hA g
    have h5 : (g ^ 2 + e ^ 2) / (2 * t) = g ^ 2 / (2 * t) + e ^ 2 / (2 * t) := by ring
    have h6 : 0 ≤ δ / 2 * (0 + g ^ 2) := by positivity
    rw [h5]
    linarith
private lemma exists_isCompact_integral_compl_sq_lt (μ : Measure ℂ) [NullSingletonClass μ] {g : ℂ → ℝ}
    (hg2 : Integrable (fun D => g D ^ 2) μ) {η : ℝ} (hη : 0 < η) :
    ∃ K : Set ℂ, IsCompact K ∧ (0 : ℂ) ∉ K ∧ ∫ D, Kᶜ.indicator (fun D => g D ^ 2) D ∂μ < η := by
  let Kn : ℕ → Set ℂ := fun n => Metric.closedBall (0 : ℂ) (n + 1) \ Metric.ball 0 (1 / (n + 1))
  have hKc : ∀ n, IsCompact (Kn n) := fun n => (isCompact_closedBall 0 _).diff Metric.isOpen_ball
  have h0K : ∀ n, (0 : ℂ) ∉ Kn n := by
    intro n h
    exact h.2 (Metric.mem_ball_self (by positivity))
  have hlim : Tendsto (fun n : ℕ => ∫ D, (Kn n)ᶜ.indicator (fun D => g D ^ 2) D ∂μ) atTop (𝓝 0) := by
    have h := tendsto_integral_of_dominated_convergence (μ := μ) (fun D => g D ^ 2)
      (F := fun n D => (Kn n)ᶜ.indicator (fun D => g D ^ 2) D) (f := fun _ => (0 : ℝ))
      (fun n => (hg2.indicator (hKc n).isClosed.measurableSet.compl).aestronglyMeasurable) hg2
      (fun n => Filter.Eventually.of_forall fun D => by
        rw [Real.norm_eq_abs, abs_of_nonneg (Set.indicator_nonneg (fun _ _ => sq_nonneg _) _)]
        exact Set.indicator_le_self' (fun _ _ => sq_nonneg _) D)
      (by
        have h0 : ∀ᵐ D ∂μ, D ≠ (0 : ℂ) := compl_mem_ae_iff.2 (measure_singleton 0)
        filter_upwards [h0] with D hD
        have hpos : 0 < ‖D‖ := norm_pos_iff.2 hD
        obtain ⟨N, hN⟩ := exists_nat_gt (max (1 / ‖D‖) ‖D‖)
        apply tendsto_const_nhds.congr'
        filter_upwards [eventually_ge_atTop N] with n hn
        have hn' : (N : ℝ) ≤ n := by exact_mod_cast hn
        have ha : 1 / ‖D‖ < n + 1 := by linarith [le_max_left (1 / ‖D‖) ‖D‖]
        have hb : ‖D‖ < n + 1 := by linarith [le_max_right (1 / ‖D‖) ‖D‖]
        have hmem : D ∈ Kn n := by
          refine ⟨?_, ?_⟩
          · rw [Metric.mem_closedBall, dist_zero_right]
            exact hb.le
          · rw [Metric.mem_ball, dist_zero_right, not_lt]
            rw [div_le_iff₀ (by positivity)]
            rw [div_lt_iff₀ hpos] at ha
            linarith
        simp [Set.indicator_apply, hmem])
    simpa using h
  obtain ⟨n, hn⟩ := (hlim.eventually (gt_mem_nhds hη)).exists
  exact ⟨Kn n, hKc n, h0K n, hn⟩
end L2m
end
end Formalism.FourierDecayAlt.P.PBK
end

set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.PBK
open Formalism.FourierDecayAlt Finset Filter Topology MeasureTheory
open scoped ComplexConjugate InnerProductSpace
noncomputable section
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
namespace Formalism.FourierDecayAlt.P.PBK
theorem _root_.solution {α : Type} {l : Filter α} (μ : Measure ℂ) [IsFiniteMeasureOnCompacts μ]
    [NullSingletonClass μ] (F G : α → ℂ → H) (g : ℂ → ℝ) (e : α → ℂ → ℝ) (hg : MemLp g 2 μ) (B : ℝ)
    (hF : ∀ᶠ x in l, MemLp (F x) 2 μ ∧ ∫ D, ‖F x D‖ ^ 2 ∂μ ≤ B)
    (he : ∀ᶠ x in l, MemLp (e x) 2 μ)
    (he0 : Tendsto (fun x => ∫ D, e x D ^ 2 ∂μ) l (𝓝 0))
    (hG : ∀ᶠ x in l, ∀ᵐ D ∂μ, ‖G x D‖ ≤ g D + e x D)
    (hloc : ∀ K : Set ℂ, IsCompact K → (0 : ℂ) ∉ K → ∀ δ : ℝ, 0 < δ →
      ∀ᶠ x in l, ∀ᵐ D ∂μ, D ∈ K → ‖F x D‖ ≤ δ) :
    Tendsto (fun x => ∫ D, ⟪F x D, G x D⟫_ℂ ∂μ) l (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  set B' : ℝ := max B 0 + 1 with hB'
  have hB'pos : 0 < B' := by positivity
  set t : ℝ := ε / (4 * B') with ht_def
  have ht : 0 < t := by positivity
  have hg2 : Integrable (fun D => g D ^ 2) μ := hg.integrable_sq
  obtain ⟨K, hKc, h0K, hKint⟩ := exists_isCompact_integral_compl_sq_lt μ hg2 (η := ε * t / 2) (by positivity)
  have hKmeas : MeasurableSet K := hKc.isClosed.measurableSet
  have hKfin : μ K < ⊤ := hKc.measure_lt_top
  have hI1 : Integrable (K.indicator (fun _ => (1 : ℝ))) μ :=
    (integrable_indicator_iff hKmeas).2 (integrableOn_const hKfin.ne)
  set M : ℝ := ∫ D, K.indicator (fun _ => (1 : ℝ)) D ∂μ + ∫ D, g D ^ 2 ∂μ + 1 with hM_def
  have hM : 0 < M := by
    have h1 : 0 ≤ ∫ D, K.indicator (fun _ => (1 : ℝ)) D ∂μ :=
      integral_nonneg fun D => Set.indicator_nonneg (fun _ _ => zero_le_one) D
    have h2 : 0 ≤ ∫ D, g D ^ 2 ∂μ := integral_nonneg fun D => sq_nonneg _
    linarith
  set δ : ℝ := ε / (4 * M) with hδ_def
  have hδ : 0 < δ := by positivity
  have he' : ∀ᶠ x in l, ∫ D, e x D ^ 2 ∂μ < ε * t / 2 := he0.eventually (gt_mem_nhds (by positivity))
  filter_upwards [hF, he, he', hG, hloc K hKc h0K δ hδ] with x hFx hex he2 hGx hlx
  obtain ⟨hFx, hFB⟩ := hFx
  rw [dist_zero_right]
  have hF2 : Integrable (fun D => ‖F x D‖ ^ 2) μ := (memLp_two_iff_integrable_sq_norm hFx.1).1 hFx
  have he2i : Integrable (fun D => e x D ^ 2) μ := hex.integrable_sq
  have hIc : Integrable (Kᶜ.indicator (fun D => g D ^ 2)) μ := hg2.indicator hKmeas.compl
  have i1 : Integrable (fun D => t * ‖F x D‖ ^ 2) μ := hF2.const_mul t
  have i2 : Integrable (fun D => (Kᶜ.indicator (fun D => g D ^ 2) D + e x D ^ 2) / (2 * t)) μ :=
    (hIc.add he2i).div_const _
  have i3 : Integrable (fun D => δ / 2 * (K.indicator (fun _ => (1 : ℝ)) D + g D ^ 2)) μ :=
    (hI1.add hg2).const_mul _
  have i12 : Integrable (fun D => t * ‖F x D‖ ^ 2 +
      (Kᶜ.indicator (fun D => g D ^ 2) D + e x D ^ 2) / (2 * t)) μ := i1.add i2
  have hbnd : ∀ᵐ D ∂μ, ‖⟪F x D, G x D⟫_ℂ‖ ≤
      t * ‖F x D‖ ^ 2 + (Kᶜ.indicator (fun D => g D ^ 2) D + e x D ^ 2) / (2 * t) +
        δ / 2 * (K.indicator (fun _ => (1 : ℝ)) D + g D ^ 2) := by
    filter_upwards [hGx, hlx] with D hGD hlD
    have h1 : ‖⟪F x D, G x D⟫_ℂ‖ ≤ ‖F x D‖ * ‖G x D‖ := norm_inner_le_norm _ _
    have hP := mul_le_young_bounds_of_le_add ht hδ.le (norm_nonneg (F x D)) hGD
    by_cases hD : D ∈ K
    · have hi1 : K.indicator (fun _ => (1 : ℝ)) D = 1 := by simp [Set.indicator_apply, hD]
      have hi2 : Kᶜ.indicator (fun D => g D ^ 2) D = 0 := by simp [Set.indicator_apply, hD]
      rw [hi1, hi2]
      exact h1.trans (hP.1 (hlD hD))
    · have hi1 : K.indicator (fun _ => (1 : ℝ)) D = 0 := by simp [Set.indicator_apply, hD]
      have hi2 : Kᶜ.indicator (fun D => g D ^ 2) D = g D ^ 2 := by simp [Set.indicator_apply, hD]
      rw [hi1, hi2]
      exact h1.trans hP.2
  have hsplit : ∫ D, (t * ‖F x D‖ ^ 2 + (Kᶜ.indicator (fun D => g D ^ 2) D + e x D ^ 2) / (2 * t) +
        δ / 2 * (K.indicator (fun _ => (1 : ℝ)) D + g D ^ 2)) ∂μ =
      t * ∫ D, ‖F x D‖ ^ 2 ∂μ + (∫ D, Kᶜ.indicator (fun D => g D ^ 2) D ∂μ + ∫ D, e x D ^ 2 ∂μ) / (2 * t) +
        δ / 2 * (M - 1) := by
    rw [integral_add i12 i3, integral_add i1 i2, integral_const_mul, integral_div,
      integral_add hIc he2i, integral_const_mul, integral_add hI1 hg2]
    simp only [hM_def]
    ring
  have hle : ‖∫ D, ⟪F x D, G x D⟫_ℂ ∂μ‖ ≤ t * ∫ D, ‖F x D‖ ^ 2 ∂μ +
      (∫ D, Kᶜ.indicator (fun D => g D ^ 2) D ∂μ + ∫ D, e x D ^ 2 ∂μ) / (2 * t) + δ / 2 * (M - 1) := by
    rw [← hsplit]
    exact (norm_integral_le_integral_norm _).trans
      (integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => norm_nonneg _) (i12.add i3) hbnd)
  have hb1 : t * ∫ D, ‖F x D‖ ^ 2 ∂μ ≤ ε / 4 := by
    have hFB' : ∫ D, ‖F x D‖ ^ 2 ∂μ ≤ B' := by linarith [le_max_left B 0]
    have : t * B' = ε / 4 := by rw [ht_def]; field_simp <;> ring
    nlinarith
  have hb2 : (∫ D, Kᶜ.indicator (fun D => g D ^ 2) D ∂μ + ∫ D, e x D ^ 2 ∂μ) / (2 * t) ≤ ε / 2 := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  have hb3 : δ / 2 * (M - 1) ≤ ε / 8 := by
    have : δ * M = ε / 4 := by rw [hδ_def]; field_simp <;> ring
    nlinarith
  linarith
end Formalism.FourierDecayAlt.P.PBK
