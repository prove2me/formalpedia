-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave6_04_actual_randomstop_source_jump_quadratic_negative_mark_tails_vanish_pathwise
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T07:01:57.629443+00:00
-- url     : https://prove2.me/submissions/26400b70-b01e-42ae-b369-d76c159f185c

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_04_actual_randomstop_discounted_C2_negative_jump_pathwise_quadratic_energy_from_true_source_clock
import Theorems.Thm_AvramDividend_Classical_avram_wave6_04_integrable_signed_measurable_antitone_set_tails_tendsto_zero

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Actual original stopped negative source C2 Taylor quadratic jump-count tails vanish pathwise. -/
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
  :
    let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
    let K : Ω → @Measure ((ℝ≥0 × Ω) × ℝ)
        (@Prod.instMeasurableSpace _ _ (𝓕.rightCont.predictable)
          (inferInstance : MeasurableSpace ℝ)) := fun ω =>
      @Measure.map (ℝ≥0 × ℝ) ((ℝ≥0 × Ω) × ℝ)
        (inferInstance : MeasurableSpace (ℝ≥0 × ℝ))
        (@Prod.instMeasurableSpace _ _ (𝓕.rightCont.predictable)
          (inferInstance : MeasurableSpace ℝ))
        (fun p : ℝ≥0 × ℝ => ((p.1, ω), p.2)) (NX ω)
    ∀     (M : @Measure ((ℝ≥0 × Ω) × ℝ)
      (@Prod.instMeasurableSpace _ _ (𝓕.rightCont.predictable)
        (inferInstance : MeasurableSpace ℝ)))
    (hM : M = P.bind K)
    (T : ℝ≥0)
    (S : Set ((ℝ≥0 × Ω) × ℝ))
    (hST : S = {p | p.1.1 ≤ T})
    (MT N : @Measure ((ℝ≥0 × Ω) × ℝ)
      (@Prod.instMeasurableSpace _ _ (𝓕.rightCont.predictable)
        (inferInstance : MeasurableSpace ℝ)))
    (hMT : MT = M.restrict S)
    (μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable))
    (hμ : μ Set.univ < ⊤)
    (hμclock : ∀ A : Set (ℝ≥0 × Ω),
      MeasurableSet[𝓕.rightCont.predictable] A →
        μ A = ((((volume : Measure ℝ).restrict
          (Icc 0 (T : ℝ))).map Real.toNNReal).prod P) A)
    (hN : N = (letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable
      μ.prod (X.ν.restrict (Iio (0 : ℝ)))))
    (B : ℕ → Set ℝ) (hBm : ∀ k, MeasurableSet (B k))
    (hBmono : Monotone B) (hBcover : (⋃ k, B k) = Set.univ)
    (hLocal : ∀ k, MT ((Set.univ : Set (ℝ≥0 × Ω)) ×ˢ B k) ≠ ∞)
    (hFuture : ∀ (i : ℝ≥0) (A : Set Ω) (C : Set ℝ),
      MeasurableSet[𝓕.rightCont i] A → MeasurableSet C →
      MT ((Set.Ioi i ×ˢ A) ×ˢ C) =
        N ((Set.Ioi i ×ˢ A) ×ˢ C))
    (τ : Ω → ℝ≥0∞) (hτ : IsStoppingTime 𝓕.rightCont τ)
    (q : ℝ) (hq : 0 ≤ q)
    (A : ℕ → Set ℝ) (hAm : ∀ n, MeasurableSet (A n))
    (hAanti : Antitone A) (hAempty : (⋂ n, A n) = ∅),
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
    ∀ᵐ ω ∂P,
      Tendsto (fun n : ℕ =>
        ∫ p, (AT n).indicator
          (fun p : ℝ≥0 × ℝ =>
            GW ((p.1, ω), p.2) * GW ((p.1, ω), p.2)) p ∂(NX ω))
        atTop (𝓝 0) := by
  classical
  intro NX K M hM T S hST MT N hMT μ hμ hμclock hN
    B hBm hBmono hBcover hLocal hFuture τ hτ q hq
    A hAm hAanti hAempty a Y J HS GW AT
  have hPath :=
    avram_wave6_04_actual_randomstop_discounted_C2_negative_jump_pathwise_quadratic_energy_from_true_source_clock
      X x D hD w C u v δ hw hw_cont hw_neg hu hδ hδone huv hv
      M hM T S hST MT N hMT μ hμ hμclock hN
      B hBm hBmono hBcover hLocal hFuture τ hτ q hq
  have hATm : ∀ n, MeasurableSet (AT n) := by
    intro n
    exact (hAm n).preimage measurable_snd
  have hATanti : Antitone AT := by
    intro n m hnm p hp
    exact hAanti hnm hp
  have hATempty : (⋂ n, AT n) = ∅ := by
    ext p
    constructor
    · intro hp
      have hm : p.2 ∈ ⋂ n, A n := Set.mem_iInter.mpr (by
        intro n
        exact (Set.mem_iInter.mp hp n))
      simpa [hAempty] using hm
    · intro hp
      simp at hp
  filter_upwards [hPath] with ω hω
  exact
    avram_wave6_04_integrable_signed_measurable_antitone_set_tails_tendsto_zero
      (NX ω)
      (fun p : ℝ≥0 × ℝ =>
        GW ((p.1, ω), p.2) * GW ((p.1, ω), p.2))
      hω AT hATm hATanti hATempty