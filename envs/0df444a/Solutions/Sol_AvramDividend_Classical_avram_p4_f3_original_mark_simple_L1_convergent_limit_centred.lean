-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f3_original_mark_simple_L1_convergent_limit_centred
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T14:42:33.072594+00:00
-- url     : https://prove2.me/submissions/d8b3d806-18d9-4e54-ad3f-c7030390d50b

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_f3_original_unbounded_predictable_mark_simple_L1_centered
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Nat BigOperators Topology
noncomputable section

/-- L1 convergent limits of actual original compensated marked cells preserve centring. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    {ι : Type*} [DecidableEq ι] (S : ℕ → Finset ι)
    (X : SpectrallyNegativeLevy P 𝓕)
    (T : ℝ≥0) (cut : ℕ)
    (a b : ℕ → ι → ℝ≥0)
    (hab : ∀ k, ∀ i ∈ S k, a k i ≤ b k i)
    (hbT : ∀ k, ∀ i ∈ S k, b k i ≤ T)
    (ε : ℝ) (hε : 0 < ε) (B : ℕ → ι → Set ℝ)
    (hB : ∀ k, ∀ i ∈ S k, MeasurableSet (B k i))
    (hBand : ∀ k, ∀ i ∈ S k, B k i ⊆ Ioo (-1 : ℝ) (-ε))
    (hCut : ∀ k, ∀ i ∈ S k, B k i ⊆ Iic (-(1 / ((cut : ℝ) + 1))))
    (H : ℕ → ι → Ω → ℝ)
    (hH : ∀ k, ∀ i ∈ S k, StronglyMeasurable[𝓕 (a k i)] (H k i))
    (hHL2 : ∀ k, ∀ i ∈ S k, MemLp (H k i) 2 P)
    (M : Ω → ℝ) (hM : Integrable M P) :
    let N : ℕ → ι → Ω → ℝ≥0∞ := fun k i ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc (a k i) (b k i) ×ˢ B k i)
    let r : ℕ → ι → ℝ := fun k i =>
      ((((b k i - a k i : ℝ≥0) : ℝ≥0∞) * X.ν (B k i))).toReal
    let F : ℕ → Ω → ℝ := fun k ω =>
      ∑ i ∈ S k, H k i ω * ((N k i ω).toReal - r k i)
    Tendsto (fun k => ∫⁻ ω, ‖F k ω - M ω‖ₑ ∂P) atTop (𝓝 0) →
    (∫ ω, M ω ∂P) = 0 := by
  let N : ℕ → ι → Ω → ℝ≥0∞ := fun k i ω =>
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc (a k i) (b k i) ×ˢ B k i)
  let r : ℕ → ι → ℝ := fun k i =>
    ((((b k i - a k i : ℝ≥0) : ℝ≥0∞) * X.ν (B k i))).toReal
  let F : ℕ → Ω → ℝ := fun k ω =>
    ∑ i ∈ S k, H k i ω * ((N k i ω).toReal - r k i)
  change Tendsto (fun k => ∫⁻ ω, ‖F k ω - M ω‖ₑ ∂P) atTop (𝓝 0) →
    (∫ ω, M ω ∂P) = 0
  intro hL1
  have hfinite (k : ℕ) :
      Integrable (F k) P ∧ (∫ ω, F k ω ∂P) = 0 := by
    simpa only [F, N, r] using
      (avram_p4_f3_original_unbounded_predictable_mark_simple_L1_centered
        (S k) X T cut (a k) (b k)
        (hab k) (hbT k) ε hε (B k)
        (hB k) (hBand k) (hCut k) (H k) (hH k) (hHL2 k))
  have hconv :
      Tendsto (fun k => ∫ ω, F k ω ∂P) atTop (𝓝 (∫ ω, M ω ∂P)) :=
    tendsto_integral_of_L1 M hM.aestronglyMeasurable
      (Filter.Eventually.of_forall (fun k => (hfinite k).1)) hL1
  have hconst : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop
      (𝓝 (∫ ω, M ω ∂P)) := by
    convert hconv using 1
    ext k
    exact (hfinite k).2.symm
  exact (tendsto_const_nhds_iff.mp hconst).symm
