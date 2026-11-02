-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_02b_actual_marked_source_cell_covariance_of_extractor
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T13:31:37.474359+00:00
-- url     : https://prove2.me/submissions/35f1ed9e-c2c3-4158-8c8d-1b091743cc16

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_actual_levy_past_indep_measurable_future_jump_family_ws01b
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p1_two_past_weights_marked_cell_covariance

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set AvramDividend.Classical
open scoped NNReal ENNReal Nat

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s T : ℝ≥0) (C : Set ℝ)
    (NX : Ω → Measure (ℝ≥0 × ℝ))
    (hNX : ∀ ω, NX ω =
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))))
    (H J : Ω → ℝ)
    (hH : Measurable[𝓕 s] H) (hJ : Measurable[𝓕 s] J)
    (hHm : Measurable H) (hJm : Measurable J)
    (hH2 : Integrable (fun ω => H ω ^ 2) P)
    (hJ2 : Integrable (fun ω => J ω ^ 2) P)
    (K : Ω → ℕ) (Y : ℕ → Ω → ℝ)
    (Fpath : (ℝ≥0 → ℝ) → (ℕ × (ℕ → ℝ)))
    (hFpath : Measurable Fpath)
    (hRep : ∀ ω, Fpath (fun t : ℝ≥0 =>
      X.X (s + t) ω - X.X s ω) =
        (K ω, fun n : ℕ => Y n ω))
    (hKsource : ∀ ω, (K ω : ℝ≥0∞) =
      NX ω (Set.Ioc s (s + T) ×ˢ C))
    (hKm : Measurable K) (r : ℝ≥0)
    (hKlaw : HasLaw K (poissonMeasure r) P)
    (hYm : ∀ n, Measurable (Y n))
    (ρ : Measure ℝ) [IsProbabilityMeasure ρ]
    (hYL : ∀ n, HasLaw (Y n) ρ P)
    (hYi : iIndepFun Y P)
    (hCountMarks : IndepFun K (fun ω (n : ℕ) => Y n ω) P)
    (f g : ℝ → ℝ) (hf : Measurable f) (hg : Measurable g)
    (hfI : Integrable f ρ) (hgI : Integrable g ρ)
    (hf2 : MemLp f 2 ρ) (hg2 : MemLp g 2 ρ)
    (hFsum : ∀ ω,
      (∫ p in Set.Ioc s (s + T) ×ˢ C, f p.2 ∂(NX ω)) =
        ∑ n ∈ Finset.range (K ω), f (Y n ω))
    (hGsum : ∀ ω,
      (∫ p in Set.Ioc s (s + T) ×ˢ C, g p.2 ∂(NX ω)) =
        ∑ n ∈ Finset.range (K ω), g (Y n ω)) :
    let A : Ω → ℝ := fun ω => H ω *
      ((∫ p in Set.Ioc s (s + T) ×ˢ C, f p.2 ∂(NX ω)) -
        (r : ℝ) * ∫ z, f z ∂ρ)
    let B : Ω → ℝ := fun ω => J ω *
      ((∫ p in Set.Ioc s (s + T) ×ˢ C, g p.2 ∂(NX ω)) -
        (r : ℝ) * ∫ z, g z ∂ρ)
    Integrable (fun ω => A ω * B ω) P ∧
      (∫ ω, A ω * B ω ∂P) =
        (∫ ω, H ω * J ω ∂P) * (r : ℝ) * (∫ z, f z * g z ∂ρ) := by
  have hrep : (fun ω => Fpath (fun t : ℝ≥0 =>
      X.X (s + t) ω - X.X s ω)) =
      (fun ω => (K ω, fun n : ℕ => Y n ω)) := funext hRep
  have hPast (W : Ω → ℝ) (hW : Measurable[𝓕 s] W) :
      IndepFun W (fun ω => (K ω, fun n : ℕ => Y n ω)) P := by
    have hi := actual_levy_past_indep_measurable_future_jump_family_ws01b
      X s W hW Fpath hFpath
    simpa only [hrep] using hi
  have hc := avram_wave4_p1_two_past_weights_marked_cell_covariance
    P ρ H J hHm hJm hH2 hJ2 K Y hKm r hKlaw hYm hYL hYi hCountMarks
    (hPast H hH) (hPast J hJ) (hPast (fun ω => H ω + J ω) (hH.add hJ))
    f g hf hg hfI hgI hf2 hg2
  dsimp only at hc ⊢
  simpa only [hFsum, hGsum] using hc
