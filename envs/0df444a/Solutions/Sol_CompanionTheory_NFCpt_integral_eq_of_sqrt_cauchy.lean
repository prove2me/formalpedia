-- Prove2me | solution 1 for CompanionTheory.NFCpt.integral_eq_of_sqrt_cauchy
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:18:56.714813+00:00
-- url     : https://prove2.me/submissions/5e522dba-0044-4ec9-bc79-dcac149b3088

import Mathlib
import Definitions.Def_CompanionTheory_AutomorphicTheory_DiscreteGroupWaves_IntegralEqOfSqrtCauchy
import Theorems.Thm_CompanionTheory_NFCpt_abs_sub_le_of_sqrt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CompanionTheory CompanionTheory.NFCpt
open MeasureTheory Filter Topology
namespace CompanionTheory.NFCpt
theorem _root_.solution {α : Type*} [MeasurableSpace α] {μ : Measure α} {q : ℕ → α → ℝ} {v : α → ℝ}
    {d : ℕ → ℕ → α → ℝ} {a : ℝ} (hq : ∀ n, Integrable (q n) μ) (hq0 : ∀ n x, 0 ≤ q n x)
    (hd : ∀ n m, Integrable (d n m) μ) (hd0 : ∀ n m x, 0 ≤ d n m x)
    (htri : ∀ n m x, |Real.sqrt (q n x) - Real.sqrt (q m x)| ≤ Real.sqrt (d n m x))
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun n => q n x) atTop (𝓝 (v x)))
    (ha : Tendsto (fun n => ∫ x, q n x ∂μ) atTop (𝓝 a))
    (hC : ∀ η : ℝ, 0 < η → ∃ N : ℕ, ∀ n m, N ≤ n → N ≤ m → ∫ x, d n m x ∂μ ≤ η) :
    Integrable v μ ∧ ∫ x, v x ∂μ = a := by
  have hv : AEStronglyMeasurable v μ := aestronglyMeasurable_of_tendsto_ae atTop (fun n => (hq n).1) hlim
  obtain ⟨B, hB⟩ : ∃ B : ℝ, ∀ n, ∫ x, q n x ∂μ ≤ B := by
    obtain ⟨B, hB⟩ := ha.bddAbove_range
    exact ⟨B, fun n => hB ⟨n, rfl⟩⟩
  have hB0 : 0 ≤ B := (integral_nonneg (hq0 0)).trans (hB 0)
  have key : ∀ η : ℝ, 0 < η → ∃ N : ℕ, ∀ n, N ≤ n → ∫⁻ x, ‖q n x - v x‖ₑ ∂μ ≤ ENNReal.ofReal η := by
    intro η hη
    set δ : ℝ := η / (4 * (B + 1)) with hδdef
    have hδ : 0 < δ := by positivity
    obtain ⟨N, hN⟩ := hC (δ * (η / 2)) (by positivity)
    refine ⟨N, fun n hn => ?_⟩
    have hnm : ∀ m, N ≤ m → ∫⁻ x, ‖q n x - q m x‖ₑ ∂μ ≤ ENNReal.ofReal η := by
      intro m hm
      have hI : Integrable (fun x => d n m x / δ + δ * (q n x + q m x)) μ :=
        ((hd n m).div_const δ).add (((hq n).add (hq m)).const_mul δ)
      have h1 : ∫⁻ x, ‖q n x - q m x‖ₑ ∂μ ≤ ∫⁻ x, ENNReal.ofReal (d n m x / δ + δ * (q n x + q m x)) ∂μ := by
        refine lintegral_mono fun x => ?_
        rw [← ofReal_norm]
        exact ENNReal.ofReal_le_ofReal (abs_sub_le_of_sqrt (hq0 n x) (hq0 m x) (hd0 n m x) hδ (htri n m x))
      refine h1.trans ?_
      rw [← ofReal_integral_eq_lintegral_ofReal hI (Eventually.of_forall fun x => by
        have := hd0 n m x; have := hq0 n x; have := hq0 m x; positivity)]
      refine ENNReal.ofReal_le_ofReal ?_
      have hI2 : Integrable (fun x => δ * (q n x + q m x)) μ := ((hq n).add (hq m)).const_mul δ
      rw [integral_add ((hd n m).div_const δ) hI2, integral_div, integral_const_mul, integral_add (hq n) (hq m)]
      have h2 : (∫ x, d n m x ∂μ) / δ ≤ η / 2 := by
        rw [div_le_iff₀ hδ]; linarith [hN n m hn hm]
      have h3 : δ * (∫ x, q n x ∂μ + ∫ x, q m x ∂μ) ≤ δ * (2 * (B + 1)) :=
        mul_le_mul_of_nonneg_left (by linarith [hB n, hB m]) hδ.le
      have h4 : δ * (2 * (B + 1)) = η / 2 := by rw [hδdef]; field_simp; ring
      linarith
    have hae : ∀ᵐ x ∂μ, ‖q n x - v x‖ₑ = liminf (fun m => ‖q n x - q m x‖ₑ) atTop := by
      filter_upwards [hlim] with x hx
      exact ((continuous_enorm.tendsto _).comp (tendsto_const_nhds.sub hx)).liminf_eq.symm
    rw [lintegral_congr_ae hae]
    refine (lintegral_liminf_le' fun m => ((hq n).1.sub (hq m).1).enorm).trans ?_
    calc liminf (fun m => ∫⁻ x, ‖q n x - q m x‖ₑ ∂μ) atTop
        ≤ liminf (fun _ : ℕ => ENNReal.ofReal η) atTop :=
          liminf_le_liminf (eventually_atTop.2 ⟨N, hnm⟩)
      _ = ENNReal.ofReal η := liminf_const _
  have hvi : Integrable v μ := by
    obtain ⟨N, hN⟩ := key 1 one_pos
    have hd₁ : Integrable (fun x => q N x - v x) μ :=
      ⟨(hq N).1.sub hv, (hN N le_rfl).trans_lt ENNReal.ofReal_lt_top⟩
    exact ((hq N).sub hd₁).congr (ae_of_all _ fun x => by simp)
  refine ⟨hvi, tendsto_nhds_unique ?_ ha⟩
  rw [Metric.tendsto_atTop]
  intro η hη
  obtain ⟨N, hN⟩ := key (η / 2) (by linarith)
  refine ⟨N, fun n hn => ?_⟩
  rw [dist_eq_norm, ← integral_sub (hq n) hvi]
  have h1 := (enorm_integral_le_lintegral_enorm (fun x => q n x - v x)).trans (hN n hn)
  rw [← ofReal_norm, ENNReal.ofReal_le_ofReal_iff (by linarith)] at h1
  linarith
end CompanionTheory.NFCpt
