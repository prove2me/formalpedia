-- Prove2me | solution 1 for AvramDividend.Classical.chat04_positive_reserve_killed_expectation_fatou_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T13:19:56.201686+00:00
-- url     : https://prove2.me/submissions/8fc6beca-791a-4589-aae0-5962e9aee67b

import Theorems.Thm_AvramDividend_Classical_chat04_positive_reserve_killed_scale_tendsto_initial
import Theorems.Thm_AvramDividend_Classical_chat04_killed_ennreal_scale_payoff_measurable
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Topology.Order.LiminfLimsup

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Filter Set Topology
open scoped NNReal ENNReal

/-- Fatou's lemma gives a lower bound for the killed q-scale expectation
as any deterministic observation sequence tends to zero. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (x : ℝ) (hx : 0 < x)
    (T : ℕ → ℝ≥0) (hT : Tendsto T atTop (𝓝 0)) :
    ENNReal.ofReal (W x) ≤
      Filter.liminf (fun n : ℕ => ∫⁻ ω,
        ({u : Ω | ∀ s : ℝ≥0, s ≤ T n → 0 ≤ x + X.X s u}).indicator
          (fun u => ENNReal.ofReal
            (Real.exp (-(q * ((T n) : ℝ))) * W (x + X.X (T n) u))) ω ∂P)
        atTop := by
  haveI : IsProbabilityMeasure P := X.isProbability
  let f : ℕ → Ω → ENNReal := fun n ω =>
    ({u : Ω | ∀ s : ℝ≥0, s ≤ T n → 0 ≤ x + X.X s u}).indicator
      (fun u => ENNReal.ofReal
        (Real.exp (-(q * ((T n) : ℝ))) * W (x + X.X (T n) u))) ω
  have hmeas (n : ℕ) : Measurable (f n) := by
    simpa only [f] using
      (chat04_killed_ennreal_scale_payoff_measurable X q W hW x (T n))
  have hpt (ω : Ω) :
      Filter.liminf (fun n : ℕ => f n ω) atTop =
      ENNReal.ofReal (W x) := by
    have hseq :=
      (chat04_positive_reserve_killed_scale_tendsto_initial
        X q W hW x hx ω).comp hT
    have hseq' : Tendsto (fun n : ℕ => f n ω)
        atTop (𝓝 (ENNReal.ofReal (W x))) := by
      simpa only [f, Function.comp_def] using hseq
    exact hseq'.liminf_eq
  have hfatou :
      ENNReal.ofReal (W x) ≤
        Filter.liminf (fun n : ℕ => ∫⁻ ω, f n ω ∂P) atTop := by
    calc
      ENNReal.ofReal (W x) =
          (∫⁻ ω, Filter.liminf (fun n : ℕ => f n ω) atTop ∂P) := by
            simp_rw [hpt]
            simp
      _ ≤ _ := MeasureTheory.lintegral_liminf_le hmeas
  simpa only [f] using hfatou
