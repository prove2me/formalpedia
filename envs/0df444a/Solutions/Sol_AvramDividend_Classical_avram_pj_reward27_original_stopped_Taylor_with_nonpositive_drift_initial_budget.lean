-- Prove2me | solution 1 for AvramDividend.Classical.avram_pj_reward27_original_stopped_Taylor_with_nonpositive_drift_initial_budget
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-09T22:38:37.571092+00:00
-- url     : https://prove2.me/submissions/42c9703b-fa73-4663-b3db-b459a58b5c5c

import Mathlib.Probability.Process.Stopping
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_pj_reward26_original_stopped_Taylor_initial_condexp_zero
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (C u v δ : ℝ)
    (hw : ContDiffOn ℝ 2 w (Ioo 0 C))
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y : ℝ, y < 0 → w y = 0)
    (hu : 0 < u) (hδ : 0 < δ) (hδone : δ ≤ 1)
    (huv : u + δ < v) (hv : v < C)
    (q : ℝ) (hq : 0 ≤ q) (T : ℝ≥0) :
    let a : (ℝ≥0 × Ω) → ℝ := fun p =>
      if p.1 ≤ T then Real.exp (-(q * (p.1 : ℝ))) else 0
    let Y : ℝ≥0 × Ω → ℝ := fun p => Function.leftLim
      (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
    let H : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
      (if Y p.1 ∈ Icc (u + δ) v then
        w (Y p.1 + p.2) - w (Y p.1) else 0) -
      (if -1 < p.2 then
        p.2 * (if Y p.1 ∈ Icc (u + δ) v then deriv w (Y p.1) else 0)
        else 0)
    let HS : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
      (if (p.1.1 : ℝ≥0∞) ≤ ruinTime X x D p.1.2 then
        (1 : ℝ) else 0) * H p
    let GW : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p => a p.1 * HS p
    let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
      ((Measure.count.restrict {s : ℝ≥0 | 0 < s ∧ X.X s ω -
        Function.leftLim (fun t : ℝ≥0 => X.X t ω) s ≠ 0}).map
        (fun s : ℝ≥0 => (s, X.X s ω -
          Function.leftLim (fun t : ℝ≥0 => X.X t ω) s)))
    let μT : Measure ℝ≥0 :=
      ((volume : Measure ℝ).restrict (Icc 0 (T : ℝ))).map Real.toNNReal
    let J : (Ω → ℝ≥0) → Ω → ℝ := fun ρ ω =>
      (∫ p, (if p.1 ≤ ρ ω then GW ((p.1, ω), p.2) else 0) ∂(NX ω)) -
      (∫ t, ∫ z,
        (if t ≤ ρ ω then GW ((t, ω), z) else 0)
        ∂(X.ν.restrict (Iio (0 : ℝ))) ∂μT)
    ∀ (σ : Ω → ℝ≥0)
      (hσ : IsStoppingTime 𝓕.rightCont
        (fun ω => (σ ω : WithTop ℝ≥0)))
      (B : Ω → ℝ) (hBI : Integrable B P)
      (hBnonpos : ∀ᵐ ω ∂P, B ω ≤ 0),
      Integrable (fun ω => J σ ω + B ω) P ∧
      (∀ᵐ ω ∂P,
        condExp (𝓕.rightCont 0) P (fun ω => J σ ω + B ω) ω ≤ 0)
    := by
  intro a Y H HS GW NX μT J σ hσ B hBI hBnonpos
  letI : IsProbabilityMeasure P := X.isProbability
  obtain ⟨hJI, hJzero⟩ :=
    avram_pj_reward26_original_stopped_Taylor_initial_condexp_zero
      X x D hD w C u v δ hw hw_cont hw_neg hu hδ hδone huv hv
      q hq T σ hσ
  have hSumI : Integrable (fun ω => J σ ω + B ω) P := hJI.add hBI
  have hPointwise : ∀ᵐ ω ∂P, J σ ω + B ω ≤ J σ ω := by
    filter_upwards [hBnonpos] with ω hB
    linarith
  have hMon : ∀ᵐ ω ∂P,
      condExp (𝓕.rightCont 0) P (fun ω => J σ ω + B ω) ω ≤
      condExp (𝓕.rightCont 0) P (J σ) ω := by
    first
    | exact condExp_mono hPointwise
    | exact condExp_mono hSumI hJI hPointwise
    | exact condExp_mono (m := 𝓕.rightCont 0) (μ := P) hPointwise
    | exact condExp_mono (m := 𝓕.rightCont 0) (μ := P)
        hSumI hJI hPointwise
  refine ⟨hSumI, ?_⟩
  filter_upwards [hMon, hJzero] with ω hle heq
  exact hle.trans (le_of_eq heq)