-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01e_integrator_new_finite_survival_markov_product
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T07:38:47.124799+00:00
-- url     : https://prove2.me/submissions/a25bffa7-424a-496e-be53-6e2f69c95dee

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_lower_survival_future_increment_pathwise_split
import Theorems.Thm_AvramDividend_Classical_esscher_compensated_exp_time_split
import Theorems.Thm_AvramDividend_Classical_chat04_unconditional_history_future_path_markov_tonelli
import Theorems.Thm_AvramDividend_Classical_chat04_countable_shifted_future_reserve_survival_measurable
import Theorems.Thm_AvramDividend_Classical_chat04_random_reserve_shifted_closed_survival_schedule_iff

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal
attribute [local instance] Classical.propDecidable

/-- The original-process finite-horizon Esscher survival law factors through
the actual past endpoint and the independent whole future increment path. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (θ x : ℝ) (s u : ℝ≥0)
    (τ : ℕ → ℝ≥0)
    (hCover : ∀ n : ℕ, 0 < n → ∀ k : ℕ,
      ∃ j : ℕ, τ j = (k : ℝ≥0) * (n : ℝ≥0)⁻¹)
    (hTerminal : ∃ j : ℕ, τ j = u)
    (hH : Measurable[𝓕 s]
      (fun ω : Ω => (X.X s ω,
        decide (∀ v : ℝ≥0, v ≤ s → 0 ≤ x + X.X v ω)))) :
    (∫⁻ ω, ({ω | ∀ v : ℝ≥0, v ≤ s + u → 0 ≤ x + X.X v ω}).indicator
      (fun ω => ENNReal.ofReal (Real.exp
        (θ * X.X (s + u) ω - ((s + u : ℝ≥0) : ℝ) *
          laplaceExponent X.c X.σ X.ν θ))) ω ∂P) =
    ∫⁻ h : ℝ × Bool, ∫⁻ y : ℝ≥0 → ℝ,
      (if h.2 then
        if ∀ j : ℕ, τ j ≤ u → 0 ≤ (x + h.1) + y (τ j) then
          ENNReal.ofReal (Real.exp
            (θ * h.1 - (s : ℝ) * laplaceExponent X.c X.σ X.ν θ) *
            Real.exp (θ * y u - (u : ℝ) * laplaceExponent X.c X.σ X.ν θ))
        else (0 : ℝ≥0∞)
      else (0 : ℝ≥0∞))
      ∂(Measure.map (fun ω => (fun t : ℝ≥0 => X.X t ω)) P)
      ∂(Measure.map (fun ω => (X.X s ω,
        decide (∀ v : ℝ≥0, v ≤ s → 0 ≤ x + X.X v ω))) P) := by
  classical
  let H : Ω → ℝ × Bool := fun ω =>
    (X.X s ω, decide (∀ v : ℝ≥0, v ≤ s → 0 ≤ x + X.X v ω))
  let F : (ℝ × Bool) × (ℝ≥0 → ℝ) → ℝ≥0∞ := fun z =>
    if z.1.2 then
      if ∀ j : ℕ, τ j ≤ u → 0 ≤ (x + z.1.1) + z.2 (τ j) then
        ENNReal.ofReal (Real.exp
          (θ * z.1.1 - (s : ℝ) * laplaceExponent X.c X.σ X.ν θ) *
          Real.exp (θ * z.2 u - (u : ℝ) * laplaceExponent X.c X.σ X.ν θ))
      else 0
    else 0
  have hReserve : Measurable (fun z : (ℝ × Bool) × (ℝ≥0 → ℝ) => x + z.1.1) :=
    measurable_const.add (measurable_fst.comp measurable_fst)
  have hPath : Measurable (fun z : (ℝ × Bool) × (ℝ≥0 → ℝ) => z.2) :=
    measurable_snd
  have hPair : Measurable
      (fun z : (ℝ × Bool) × (ℝ≥0 → ℝ) => (x + z.1.1, z.2)) :=
    hReserve.prodMk hPath
  have hEvent : MeasurableSet
      {z : (ℝ × Bool) × (ℝ≥0 → ℝ) |
        ∀ j : ℕ, τ j ≤ u → 0 ≤ (x + z.1.1) + z.2 (τ j)} := by
    simpa only [preimage, mem_setOf_eq] using
      (chat04_countable_shifted_future_reserve_survival_measurable τ u).preimage hPair
  have hBool : Measurable (fun z : (ℝ × Bool) × (ℝ≥0 → ℝ) => z.1.2) :=
    measurable_snd.comp measurable_fst
  have hFlag : MeasurableSet
      {z : (ℝ × Bool) × (ℝ≥0 → ℝ) | z.1.2 = true} :=
    hBool (measurableSet_singleton true)
  have hEnd : Measurable (fun z : (ℝ × Bool) × (ℝ≥0 → ℝ) => z.2 u) :=
    (measurable_pi_apply u).comp hPath
  have hBegin : Measurable (fun z : (ℝ × Bool) × (ℝ≥0 → ℝ) => z.1.1) :=
    measurable_fst.comp measurable_fst
  have hPay : Measurable
      (fun z : (ℝ × Bool) × (ℝ≥0 → ℝ) =>
        ENNReal.ofReal (Real.exp
          (θ * z.1.1 - (s : ℝ) * laplaceExponent X.c X.σ X.ν θ) *
          Real.exp (θ * z.2 u - (u : ℝ) * laplaceExponent X.c X.σ X.ν θ))) := by
    apply ENNReal.measurable_ofReal.comp
    apply Measurable.mul
    · exact Real.continuous_exp.measurable.comp
        ((measurable_const.mul hBegin).sub measurable_const)
    · exact Real.continuous_exp.measurable.comp
        ((measurable_const.mul hEnd).sub measurable_const)
  have hF : Measurable F :=
    Measurable.ite hFlag (Measurable.ite hEvent hPay measurable_const) measurable_const
  have hMarkov := chat04_unconditional_history_future_path_markov_tonelli X s H hH F hF
  change (∫⁻ ω, ({ω | ∀ v : ℝ≥0, v ≤ s + u → 0 ≤ x + X.X v ω}).indicator
    (fun ω => ENNReal.ofReal (Real.exp
      (θ * X.X (s + u) ω - ((s + u : ℝ≥0) : ℝ) *
        laplaceExponent X.c X.σ X.ν θ))) ω ∂P) =
      ∫⁻ h, ∫⁻ y, F (h, y)
        ∂(Measure.map (fun ω => (fun t : ℝ≥0 => X.X t ω)) P)
        ∂(Measure.map H P)
  rw [← hMarkov]
  apply lintegral_congr
  intro ω
  have hSplit := lower_survival_future_increment_pathwise_split X.X x s u
  have hGrid := chat04_random_reserve_shifted_closed_survival_schedule_iff
    X (fun ω : Ω => x + X.X s ω) ω s u τ hCover hTerminal
  have hExp := esscher_compensated_exp_time_split X θ s u ω
  by_cases hp : ∀ v : ℝ≥0, v ≤ s → 0 ≤ x + X.X v ω
  · by_cases hfut : ∀ v : ℝ≥0, v ≤ u →
        0 ≤ (x + X.X s ω) + (X.X (s + v) ω - X.X s ω)
    · have hw : ω ∈ {ω | ∀ v : ℝ≥0, v ≤ s + u → 0 ≤ x + X.X v ω} := by
        rw [hSplit]
        exact ⟨hp, hfut⟩
      rw [Set.indicator_of_mem hw]
      have hPastBool : (H ω).2 = true := by
        simpa [H] using hp
      have hGridRight : ∀ j : ℕ, τ j ≤ u →
          0 ≤ (x + (H ω).1) +
            ((fun t : ℝ≥0 => X.X (s + t) ω - X.X s ω) (τ j)) := by
        simpa only [H] using (hGrid.mp hfut)
      have hFRight :
          F (H ω, fun t => X.X (s + t) ω - X.X s ω) =
            ENNReal.ofReal (Real.exp
              (θ * X.X s ω - (s : ℝ) * laplaceExponent X.c X.σ X.ν θ) *
              Real.exp (θ * (X.X (s + u) ω - X.X s ω) -
                (u : ℝ) * laplaceExponent X.c X.σ X.ν θ)) := by
        dsimp [F]
        rw [if_pos hPastBool, if_pos hGridRight]
      rw [hFRight]
      simpa only [NNReal.coe_add] using congrArg ENNReal.ofReal hExp
    · have hn : ω ∉ {ω | ∀ v : ℝ≥0, v ≤ s + u → 0 ≤ x + X.X v ω} := by
        intro hw
        rw [hSplit] at hw
        exact hfut hw.2
      rw [Set.indicator_of_notMem hn]
      have hNotGrid : ¬ (∀ j : ℕ, τ j ≤ u →
          0 ≤ (x + X.X s ω) + (X.X (s + τ j) ω - X.X s ω)) :=
        mt hGrid.mpr hfut
      have hNotGridSimple : ¬ (∀ j : ℕ, τ j ≤ u →
          0 ≤ x + X.X (s + τ j) ω) := by
        intro hSimple
        apply hNotGrid
        intro j hj
        have hSafe := hSimple j hj
        convert hSafe using 1 <;> ring
      simp [F, H, hp, hNotGridSimple]
  · have hn : ω ∉ {ω | ∀ v : ℝ≥0, v ≤ s + u → 0 ≤ x + X.X v ω} := by
      intro hw
      rw [hSplit] at hw
      exact hp hw.1
    rw [Set.indicator_of_notMem hn]
    simp [F, H, hp]
