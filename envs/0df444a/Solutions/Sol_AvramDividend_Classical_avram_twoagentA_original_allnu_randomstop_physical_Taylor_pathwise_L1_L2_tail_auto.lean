-- Prove2me | solution 1 for AvramDividend.Classical.avram_twoagentA_original_allnu_randomstop_physical_Taylor_pathwise_L1_L2_tail_auto
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T12:08:27.234028+00:00
-- url     : https://prove2.me/submissions/d18e6850-b903-4eef-91c5-542b7e84b513

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_pj_workerC_actual_Levy_complete_physical_marked_clock_factory
import Theorems.Thm_AvramDividend_Classical_avram_wave6_04_actual_randomstop_true_source_full_C2_negative_jump_pathwise_L1_L2_and_cutoff_tails
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (C u v δ : ℝ)
    (hw : ContDiffOn ℝ 2 w (Ioo 0 C))
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y : ℝ, y < 0 → w y = 0)
    (hu : 0 < u) (hδ : 0 < δ) (hδone : δ ≤ 1)
    (huv : u + δ < v) (hv : v < C)
    (T : ℝ≥0) (τ : Ω → ℝ≥0∞)
    (hτ : IsStoppingTime 𝓕.rightCont τ)
    (q : ℝ) (hq : 0 ≤ q)
    (A : ℕ → Set ℝ) (hAm : ∀ n, MeasurableSet (A n))
    (hAanti : Antitone A) (hAempty : (⋂ n, A n) = ∅) :
    let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
    let a : (ℝ≥0 × Ω) → ℝ := fun p =>
      (if p.1 ≤ T then Real.exp (-(q * (p.1 : ℝ))) else 0) *
      (if (p.1 : ℝ≥0∞) ≤ τ p.2 then (1 : ℝ) else 0)
    let Y : ℝ≥0 × Ω → ℝ := fun p => Function.leftLim
      (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
    let J : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
      (if Y p.1 ∈ Icc (u + δ) v then
        w (Y p.1 + p.2) - w (Y p.1) else 0) -
      (if -1 < p.2 then
        p.2 * (if Y p.1 ∈ Icc (u + δ) v then deriv w (Y p.1) else 0)
        else 0)
    let HS : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
      (if (p.1.1 : ℝ≥0∞) ≤ ruinTime X x D p.1.2 then (1 : ℝ) else 0) * J p
    let GW : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p => a p.1 * HS p
    let AT : ℕ → Set (ℝ≥0 × ℝ) := fun n => {p | p.2 ∈ A n}
    let F : Ω → (ℝ≥0 × ℝ) → ℝ := fun ω p => GW ((p.1, ω), p.2)
    ∀ᵐ ω ∂P,
      Integrable (F ω) (NX ω) ∧
      Integrable (fun p => F ω p * F ω p) (NX ω) ∧
      Tendsto (fun n : ℕ =>
        ∫ p, (AT n).indicator (F ω) p ∂(NX ω)) atTop (𝓝 0) ∧
      Tendsto (fun n : ℕ =>
        ∫ p, (AT n).indicator (fun p => |F ω p|) p ∂(NX ω))
        atTop (𝓝 0) ∧
      Tendsto (fun n : ℕ =>
        ∫ p, (AT n).indicator (fun p => F ω p * F ω p) p ∂(NX ω))
        atTop (𝓝 0) := by
  obtain ⟨μ, hμ, hμclock, B, hBm, hBfin,
      hBmono, hBcover, hLocal, hFuture⟩ :=
    avram_pj_workerC_actual_Levy_complete_physical_marked_clock_factory X T
  exact
    avram_wave6_04_actual_randomstop_true_source_full_C2_negative_jump_pathwise_L1_L2_and_cutoff_tails
      X x D hD w C u v δ hw hw_cont hw_neg hu hδ hδone huv hv
      _ rfl T _ rfl _ _ rfl μ hμ hμclock rfl
      B hBm hBmono hBcover hLocal
      (fun i A C hA hC => hFuture i A hA C hC)
      τ hτ q hq A hAm hAanti hAempty

