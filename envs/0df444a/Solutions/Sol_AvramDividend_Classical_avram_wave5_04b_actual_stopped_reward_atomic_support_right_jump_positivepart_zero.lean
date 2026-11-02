-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_04b_actual_stopped_reward_atomic_support_right_jump_positivepart_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T17:48:44.766019+00:00
-- url     : https://prove2.me/submissions/a70f1aed-47d8-4520-94d2-6eac490e030f

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04b_actual_dividend_atomic_atomless_full_stieltjes_lintegral_split
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04b_real_clock_countable_right_positive_part_zero

open MeasureTheory Set
open scoped NNReal ENNReal BigOperators
open AvramDividend.Classical

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

/-- On the actual finite-horizon dividend measure, the ruin-stopped
right-payment atoms have countable full support, including t=0, and every
chronological original-w right-jump positive-part correction vanishes. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (ω : Ω) (T : ℝ≥0) (q : ℝ)
    (hjump : ∀ t : ℝ≥0,
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω -
            (rightLimit D t ω - D t ω))) :
    let μ : Measure ℝ :=
      (dividendMeasure D ω).restrict (Icc (0 : ℝ) (T : ℝ))
    ∃ (A : Set ℝ),
      A.Countable ∧
      A ⊆ paymentTimes (ruinTime X x D ω) ∩ Iic (T : ℝ) ∧
      (∀ t : ℝ, t ∈ paymentTimes (ruinTime X x D ω) ∩ Iic (T : ℝ) →
        μ {t} ≠ 0 → t ∈ A) ∧
      (∑' t : A, ENNReal.ofReal (Real.exp (-(q * (t : ℝ))) *
        ((rightLimit D ((t : ℝ).toNNReal) ω -
            D ((t : ℝ).toNNReal) ω) +
          w (riskProcess X x D ((t : ℝ).toNNReal) ω -
            (rightLimit D ((t : ℝ).toNNReal) ω -
              D ((t : ℝ).toNNReal) ω)) -
          w (riskProcess X x D ((t : ℝ).toNNReal) ω)))) = 0 := by
  dsimp only
  rcases avram_wave5_04b_actual_dividend_atomic_atomless_full_stieltjes_lintegral_split
      X x D hD ω T (fun _ => 0) with
    ⟨A₀, μatom, μdiffuse, hCount, hMeas, hSplit, hSum,
      hSupport, hNull, hSingle, hIntegral⟩
  let μ : Measure ℝ :=
    (dividendMeasure D ω).restrict (Icc (0 : ℝ) (T : ℝ))
  let A : Set ℝ :=
    A₀ ∩ (paymentTimes (ruinTime X x D ω) ∩ Iic (T : ℝ))
  have hCountA : A.Countable := hCount.mono (by
    intro t ht
    exact ht.1)
  have hSubset : A ⊆
      paymentTimes (ruinTime X x D ω) ∩ Iic (T : ℝ) := by
    intro t ht
    exact ht.2
  have hAllAtoms : ∀ t : ℝ,
      t ∈ paymentTimes (ruinTime X x D ω) ∩ Iic (T : ℝ) →
      μ {t} ≠ 0 → t ∈ A := by
    intro t ht hnonzero
    have htA₀ : t ∈ A₀ := by
      by_contra hnot
      have hSub : ({t} : Set ℝ) ⊆ A₀ᶜ := by
        intro s hs
        have heq : s = t := by simpa using hs
        subst s
        simpa using hnot
      have hAtomZero : μatom {t} = 0 := by
        apply le_antisymm
        · exact (measure_mono hSub).trans_eq hSupport
        · exact zero_le
      letI : NullSingletonClass μdiffuse := hNull
      have hDiffuseZero : μdiffuse {t} = 0 := measure_singleton t
      have hZero : μ {t} = 0 := by
        change ((dividendMeasure D ω).restrict (Icc (0 : ℝ) (T : ℝ))) {t} = 0
        rw [hSplit, Measure.add_apply, hAtomZero, hDiffuseZero]
        simp
      exact hnonzero hZero
    exact ⟨htA₀, ht⟩
  have hNonneg : ∀ t : A, 0 ≤ (t : ℝ) := by
    intro t
    have htPay := (t.property).2.1
    change (t : ℝ) ∈ Ici (0 : ℝ) ∩
      ({0} ∪ {s : ℝ | ENNReal.ofReal s < ruinTime X x D ω}) at htPay
    exact htPay.1
  have hA : ∀ t : A,
      ((t : ℝ).toNNReal) = 0 ∨
        (((t : ℝ).toNNReal) : ℝ≥0∞) < ruinTime X x D ω := by
    intro t
    have htPay := (t.property).2.1
    change (t : ℝ) ∈ Ici (0 : ℝ) ∩
      ({0} ∪ {s : ℝ | ENNReal.ofReal s < ruinTime X x D ω}) at htPay
    rcases htPay.2 with hzero | hlt
    · left
      have heq : (t : ℝ) = 0 := by simpa using hzero
      simp only [heq, Real.toNNReal_zero]
    · right
      change (((t : ℝ).toNNReal) : ℝ≥0∞) < ruinTime X x D ω at hlt
      exact hlt
  refine ⟨A, hCountA, hSubset, hAllAtoms, ?_⟩
  exact avram_wave5_04b_real_clock_countable_right_positive_part_zero
    X x D w ω q hjump A hCountA hNonneg hA
