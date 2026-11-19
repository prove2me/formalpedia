-- Prove2me | solution 1 for AvramDividend.Classical.avram_pj_reward49_original_finiteband_jump_kernel_uniform_count_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T20:21:24.159822+00:00
-- url     : https://prove2.me/submissions/2bb69bb9-99c6-4d72-9104-599b4a40d80c

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_pj_reward63_compact_clipped_firstorder_discounted_mark_uniform_bound
import Theorems.Thm_AvramDividend_Classical_avram_pj_reward51_original_finiteband_NX_count_measurable
import Theorems.Thm_AvramDividend_Classical_avram_pj_reward43_original_finite_negative_mark_count_L1
import Theorems.Thm_AvramDividend_Classical_avram_pj_reward61_original_intrinsic_closed_positive_time_count_eq
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_ruin_truncated_NNReal_clock_le_finite_horizon
set_option pp.universes true

set_option pp.explicit true
set_option pp.fullNames true
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section

theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) (hBV : ¬ X.BoundedVariation) (hSigmaZero : X.σ = 0) (q : ℝ) (hq : 0 < q) (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C) (hCfinite : C ≠ ⊤) (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0)) (hw_neg : ∀ y < 0, w y = 0) (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0) (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y) (x : ℝ) (hx : 0 < x) (hxc : ENNReal.ofReal x ≤ C) (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D) (hw_nonneg : ∀ ω (t : ℝ≥0), 0 < t → (t : ℝ≥0∞) < ruinTime X x D ω → 0 ≤ w (riskProcess X x D t ω)) (hjump : ∀ ω (t : ℝ≥0), (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) → rightLimit D t ω - D t ω ≤ w (riskProcess X x D t ω) - w (riskProcess X x D t ω - (rightLimit D t ω - D t ω))) (n : ℕ) (hn : 0 < n) (τ : Ω → ℝ≥0) (hτeq : ∀ ω, τ ω = (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal) (hτmeas : Measurable (fun ω => (τ ω : ℝ))) (hτstop : IsStoppingTime 𝓕.rightCont (fun ω => (τ ω : WithTop ℝ≥0))) (ρ : Ω → ℝ≥0) (hρstop : IsStoppingTime 𝓕.rightCont (fun ω => (ρ ω : WithTop ℝ≥0))) (hρle : ∀ ω, ρ ω ≤ τ ω) (G : Ω → ℝ) (hGdef : ∀ ω, G ω = (if ρ ω = 0 then w x else Real.exp (-(q * (ρ ω : ℝ))) * w (if (ρ ω : ℝ≥0∞) < ruinTime X x D ω then x + X.X (ρ ω) ω - rightLimit D (ρ ω) ω else riskProcess X x D (ρ ω) ω) + (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (ρ ω : ℝ), ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal)) (hGI : Integrable G P) (A : Set Ω) (hA : MeasurableSet[𝓕.rightCont 0] A) (Cband u v δ η : ℝ)
    (hu : 0 < u) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (huv : u + δ < v) (hη : 0 < η) (hη1 : η < 1)
    (hv : v < Cband) (hvC : v < C.toReal)
    (hwCb : ContDiffOn ℝ 2 w (Ioo 0 Cband)) :
      (let T : ℝ≥0 := (n : ℝ≥0)
      let Y : ℝ≥0 × Ω → ℝ := fun p => Function.leftLim
        (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
      let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
        ((Measure.count.restrict {s : ℝ≥0 | 0 < s ∧ X.X s ω -
          Function.leftLim (fun t : ℝ≥0 => X.X t ω) s ≠ 0}).map
          (fun s : ℝ≥0 => (s, X.X s ω -
            Function.leftLim (fun t : ℝ≥0 => X.X t ω) s)))
      let Lsource : Ω → ℝ := fun ω =>
        (∫ p, (if p.1 ≤ ρ ω ∧ p.2 ∈ Ioo (-1 : ℝ) (-η) then
          Real.exp (-(q * (p.1 : ℝ))) *
            (if Y (p.1, ω) ∈ Icc (u + δ) v then
              deriv w (Y (p.1, ω)) * p.2 else 0) else 0) ∂(NX ω))
      ∃ K : ℝ, 0 ≤ K ∧
        (∀ᵐ ω ∂P, |Lsource ω| ≤ K * ((NX ω)
          (Ioc (0 : ℝ≥0) T ×ˢ Ioo (-1 : ℝ) (-η))).toReal)) := by
  classical
  let T : ℝ≥0 := (n : ℝ≥0)
  let Z : Set ℝ := Ioo (-1 : ℝ) (-η)
  let S : Set (ℝ≥0 × ℝ) := Icc (0 : ℝ≥0) T ×ˢ Z
  let Y : ℝ≥0 × Ω → ℝ := fun p =>
    Function.leftLim (fun s => x + X.X s p.2 - rightLimit D s p.2) p.1
  let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
    ((Measure.count.restrict {s : ℝ≥0 | 0 < s ∧ X.X s ω -
      Function.leftLim (fun t : ℝ≥0 => X.X t ω) s ≠ 0}).map
      (fun s : ℝ≥0 => (s, X.X s ω -
        Function.leftLim (fun t : ℝ≥0 => X.X t ω) s)))
  let F : Ω → (ℝ≥0 × ℝ) → ℝ := fun ω p =>
    if p.1 ≤ ρ ω ∧ p.2 ∈ Z then Real.exp (-(q * (p.1 : ℝ))) *
      (if Y (p.1, ω) ∈ Icc (u + δ) v then deriv w (Y (p.1, ω)) * p.2 else 0) else 0
  obtain ⟨M, hM, hBound⟩ :=
    avram_pj_reward63_compact_clipped_firstorder_discounted_mark_uniform_bound
      (fun t ω => Y (t, ω)) q (le_of_lt hq) w Cband u v δ η
      hwCb (by linarith) huv hv hη
  have hB : ∀ ω p, |F ω p| ≤ M := by
    intro ω p
    by_cases h : p.1 ≤ ρ ω ∧ p.2 ∈ Z
    · simpa only [F, if_pos h] using hBound p.1 ω p.2 h.2
    · simpa [F, h] using hM
  have hρT (ω : Ω) : ρ ω ≤ T := (hρle ω).trans
    (avram_p4_d_dividend_original_ruin_truncated_NNReal_clock_le_finite_horizon
      X x D n τ hτeq ω)
  have hS : MeasurableSet S := measurableSet_Icc.prod measurableSet_Ioo
  have hMassAE : ∀ᵐ ω ∂P, NX ω S < ⊤ := by
    have hm : Measurable (fun ω => NX ω (Ioc (0 : ℝ≥0) T ×ˢ Z)) := by
      simpa only [NX, Z, T] using
        (avram_pj_reward51_original_finiteband_NX_count_measurable X T η)
    have hi : (∫⁻ ω, NX ω (Ioc (0 : ℝ≥0) T ×ˢ Z) ∂P) < ⊤ := by
      simpa only [NX, T, Z] using
        (avram_pj_reward43_original_finite_negative_mark_count_L1 X T η hη hη1)
    filter_upwards [ae_lt_top hm (ne_of_lt hi)] with ω hω
    have heq := avram_pj_reward61_original_intrinsic_closed_positive_time_count_eq
      X ω T Z measurableSet_Ioo
    change NX ω S = NX ω (Ioc 0 T ×ˢ Z) at heq
    rw [heq]
    exact hω
  refine ⟨M, hM, ?_⟩
  filter_upwards [hMassAE] with ω hfinite
  have hSupport (p : ℝ≥0 × ℝ) (hp : p ∉ S) : F ω p = 0 := by
    by_cases ht : p.1 ≤ ρ ω
    · by_cases hz : p.2 ∈ Z
      · have hmem : p ∈ S := ⟨⟨bot_le, ht.trans (hρT ω)⟩, hz⟩
        exact (hp hmem).elim
      · simp [F, ht, hz]
    · simp [F, ht]
  have hIntegral :
      (∫ p, F ω p ∂(NX ω)) =
      ∫ p in S, F ω p ∂(NX ω) := by
    rw [← integral_indicator hS]
    apply integral_congr_ae
    filter_upwards [] with p
    by_cases hp : p ∈ S
    · simp [Set.indicator, hp]
    · simp [Set.indicator, hp, hSupport p hp]
  haveI : IsFiniteMeasure ((NX ω).restrict S) :=
    ⟨by simpa [Measure.restrict_apply, hS] using hfinite⟩
  have hNorm := norm_integral_le_of_norm_le_const
    (μ := (NX ω).restrict S) (C := M)
    (Filter.Eventually.of_forall (fun p => by
      rw [Real.norm_eq_abs]; exact hB ω p))
  have hGoal : |∫ p, F ω p ∂(NX ω)| ≤ M * (NX ω S).toReal := by
    rw [hIntegral]
    simpa [Measure.real, measureReal_def, Measure.restrict_apply, hS,
      Real.norm_eq_abs] using hNorm
  have hCount : NX ω S = NX ω (Ioc 0 T ×ˢ Z) := by
    simpa [NX, S, Z, T] using
      (avram_pj_reward61_original_intrinsic_closed_positive_time_count_eq
        X ω T Z measurableSet_Ioo)
  rw [hCount] at hGoal
  simpa only [F, NX, Z, Y, T] using hGoal
