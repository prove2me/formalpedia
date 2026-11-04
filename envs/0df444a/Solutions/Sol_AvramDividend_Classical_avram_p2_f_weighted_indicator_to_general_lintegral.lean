-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_f_weighted_indicator_to_general_lintegral
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T12:19:09.433755+00:00
-- url     : https://prove2.me/submissions/7416a52f-f4f8-4c36-b452-634eb3c5fb06

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped ENNReal

/-- Event formulas imply weights for the measurability structure actually
carried by the original published theorem. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (mPast : MeasurableSpace Ω) (hm : mPast ≤ mΩ)
    (μ : Measure Ω) (N : Ω → ℝ≥0∞) (hN : Measurable N)
    (r : ℝ≥0∞)
    (hEvent : ∀ A : Set Ω, MeasurableSet[mPast] A →
      (∫⁻ ω in A, N ω ∂μ) = μ A * r)
    (H : Ω → ℝ≥0∞) (hH : Measurable[mPast] H) :
    (∫⁻ ω, H ω * N ω ∂μ) = (∫⁻ ω, H ω ∂μ) * r := by
  let motive : (Ω → ℝ≥0∞) → Prop := fun h =>
    (∫⁻ ω, h ω * N ω ∂μ) = (∫⁻ ω, h ω ∂μ) * r
  change motive H
  refine @Measurable.ennreal_induction Ω mPast motive ?_ ?_ ?_ H hH
  · intro c A hA
    dsimp [motive]
    have hAa : MeasurableSet A := hA
    have heq : (fun ω : Ω => (A.indicator (fun _ => c)) ω * N ω) =
        (fun ω : Ω => A.indicator (fun ω => c * N ω) ω) := by
      funext ω
      by_cases hw : ω ∈ A <;> simp [Set.indicator, hw]
    rw [heq, lintegral_indicator hAa, lintegral_const_mul c hN,
      hEvent A hA, lintegral_indicator_const hAa c]
    ac_rfl
  · intro f g hdisj hf hg ihf ihg
    dsimp [motive] at ihf ihg ⊢
    have hf' : Measurable f := hf
    calc
      (∫⁻ ω, (f + g) ω * N ω ∂μ)
          = (∫⁻ ω, f ω * N ω + g ω * N ω ∂μ) := by
            congr 1
            funext ω
            simp only [Pi.add_apply, add_mul]
      _ = (∫⁻ ω, f ω * N ω ∂μ) +
          (∫⁻ ω, g ω * N ω ∂μ) :=
            lintegral_add_left (hf'.mul hN) _
      _ = (∫⁻ ω, f ω ∂μ) * r +
          (∫⁻ ω, g ω ∂μ) * r := by rw [ihf, ihg]
      _ = ((∫⁻ ω, f ω ∂μ) + (∫⁻ ω, g ω ∂μ)) * r := by rw [add_mul]
      _ = (∫⁻ ω, (f + g) ω ∂μ) * r := by
            change ((∫⁻ ω, f ω ∂μ) + (∫⁻ ω, g ω ∂μ)) * r =
              (∫⁻ ω, f ω + g ω ∂μ) * r
            rw [lintegral_add_left hf' g]
  · intro f hfm hmono ih
    dsimp [motive] at ih ⊢
    have hfm' (n : ℕ) : Measurable (f n) := hfm n
    have hprod (n : ℕ) :
        Measurable (fun ω => f n ω * N ω) := (hfm' n).mul hN
    have hprodmono : Monotone (fun n ω => f n ω * N ω) := by
      intro i j hij ω
      calc
        f i ω * N ω = N ω * f i ω := mul_comm _ _
        _ ≤ N ω * f j ω := mul_le_mul_right ((hmono hij) ω) (N ω)
        _ = f j ω * N ω := mul_comm _ _
    change (∫⁻ ω, (⨆ n, f n ω) * N ω ∂μ) =
      (∫⁻ ω, ⨆ n, f n ω ∂μ) * r
    calc
      (∫⁻ ω, (⨆ n, f n ω) * N ω ∂μ)
          = (∫⁻ ω, ⨆ n, f n ω * N ω ∂μ) := by
              congr 1
              funext ω
              exact ENNReal.iSup_mul (fun n => f n ω) (N ω)
      _ = ⨆ n, (∫⁻ ω, f n ω * N ω ∂μ) :=
            lintegral_iSup hprod hprodmono
      _ = ⨆ n, (∫⁻ ω, f n ω ∂μ) * r := by
            congr 1
            funext n
            exact ih n
      _ = (⨆ n, (∫⁻ ω, f n ω ∂μ)) * r :=
            (ENNReal.iSup_mul _ r).symm
      _ = (∫⁻ ω, ⨆ n, f n ω ∂μ) * r := by
            rw [lintegral_iSup hfm' hmono]
