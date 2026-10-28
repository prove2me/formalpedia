-- Prove2me | solution 1 for FunctionalInequalities.KLS.CEK.exists_normalized_maximizing_sequence_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:05:30.053848+00:00
-- url     : https://prove2.me/submissions/9633b76f-4308-4b8f-b6af-ab26964b3013

import Definitions.Def_KLSModular_FunctionalInequalities_Probability_MomentMeasure_Baseline
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_CEK_VariationalMaximum
import Theorems.Thm_FunctionalInequalities_Analysis_legendre_norm_readable
import Theorems.Thm_FunctionalInequalities_KLS_CEK_exists_uniform_functional_upper_readable

section
noncomputable section
section
open FunctionalInequalities.Analysis
section
open MeasureTheory Set Filter
open scoped ENNReal Topology
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
/-- Actual density of the conjugate, including its zero-density exterior. -/
theorem FunctionalInequalities.Probability.MomentMeasure.density_legendre_norm :
    density (legendre (fun x : E => (‖x‖ : EReal))) =
      (Metric.closedBall (0 : E) 1).indicator (fun _ => (1 : ℝ≥0∞)) := by
  funext y
  by_cases hy : ‖y‖ ≤ 1
  · have hm : y ∈ Metric.closedBall (0 : E) 1 := by simpa only [Metric.mem_closedBall, dist_zero_right] using hy
    simp only [density, legendre_norm_readable, if_pos hy, neg_zero, EReal.exp_zero, indicator_of_mem hm]
  · have hm : y ∉ Metric.closedBall (0 : E) 1 := by simpa only [Metric.mem_closedBall, dist_zero_right] using hy
    simp only [density, legendre_norm_readable, if_neg hy, EReal.neg_top, EReal.exp_bot, indicator_of_notMem hm]
variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
/-- The baseline exponential mass is the actual positive finite Haar volume of
the closed unit ball, not a supplied mass value or probability normalization. -/
theorem FunctionalInequalities.Probability.MomentMeasure.mass_legendre_norm (dx : Measure E) [dx.IsAddHaarMeasure] :
    mass dx (legendre (fun x : E => (‖x‖ : EReal))) = dx (Metric.closedBall 0 1) ∧
      0 < mass dx (legendre (fun x : E => (‖x‖ : EReal))) ∧
      mass dx (legendre (fun x : E => (‖x‖ : EReal))) ≠ ⊤ := by
  have heq : mass dx (legendre (fun x : E => (‖x‖ : EReal))) = dx (Metric.closedBall 0 1) := by
    unfold mass
    rw [density_legendre_norm]
    rw [lintegral_indicator_const measurableSet_closedBall, one_mul]
  rw [heq]
  refine ⟨rfl, ?_, ?_⟩
  · have hpos : 0 < dx (Metric.ball (0 : E) 1) :=
      Measure.measure_pos_of_mem_nhds dx (Metric.ball_mem_nhds 0 zero_lt_one)
    exact hpos.trans_le (measure_mono Metric.ball_subset_closedBall)
  · exact (isCompact_closedBall (0 : E) 1).measure_ne_top
/-- The actual norm potential is admissible and has an actual finite real
functional value whenever the source first moment is finite, including finite
nonprobability measures and dimension zero. -/
theorem FunctionalInequalities.Probability.MomentMeasure.norm_baseline_finite (dx μ : Measure E) [dx.IsAddHaarMeasure]
    (hfirst : Integrable (fun x : E => x) μ) :
    ConvexPotential (fun x : E => (‖x‖ : EReal)) ∧
      PotentialIntegrable (fun x : E => (‖x‖ : EReal)) μ ∧
      (∃ L : ℝ, variationalFunctional dx μ (fun x : E => (‖x‖ : EReal)) = (L : EReal)) := by
  have hc : ConvexPotential (fun x : E => (‖x‖ : EReal)) := by
    refine ⟨fun _ => EReal.coe_ne_bot _, ?_⟩
    simpa only [mem_univ, true_and, EReal.coe_le_coe_iff] using
      (convexOn_norm (E := E) convex_univ).convex_epigraph
  have hp : PotentialIntegrable (fun x : E => (‖x‖ : EReal)) μ :=
    ⟨fun _ => EReal.coe_ne_bot _, Eventually.of_forall fun _ => EReal.coe_ne_top _, by
      simpa only [EReal.toReal_coe] using hfirst.norm⟩
  obtain ⟨_heq, hpos, hfin⟩ := mass_legendre_norm dx
  refine ⟨hc, hp, Real.log (mass dx (legendre (fun x : E => (‖x‖ : EReal)))).toReal - ∫ x, ‖x‖ ∂μ, ?_⟩
  simp only [variationalFunctional, EReal.toReal_coe, ENNReal.log_pos_real hpos.ne' hfin, ← EReal.coe_sub]
end
end
end
end

noncomputable section
open FunctionalInequalities.Analysis
open FunctionalInequalities.Probability
open FunctionalInequalities.Probability.MomentMeasure
section
open MeasureTheory Filter Set
open scoped ENNReal Topology
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
/-- The actual normalized functional range has a finite real supremum and an
actual sequence of normalized potentials approaching it. No sequence, supremum
value, mass convergence or desired bound is supplied. -/
theorem solution (dx μ : Measure E)
    [dx.IsAddHaarMeasure] [IsProbabilityMeasure μ]
    (hsub : ∀ V : Submodule ℝ E, μ (V : Set E)ᶜ = 0 → V = ⊤)
    (hfirst : Integrable (fun x : E => x) μ) (hbar : ∫ x, x ∂μ = 0) :
    ∃ (S : ℝ) (φ : ℕ → E → EReal),
      (∀ j, FunctionalInequalities.Analysis.ConvexPotential (φ j)) ∧ (∀ j, FunctionalInequalities.Probability.MomentMeasure.PotentialIntegrable (φ j) μ) ∧
      (∀ j x, 0 ≤ φ j x) ∧ (∀ j, φ j 0 = 0) ∧
      Tendsto (fun j => FunctionalInequalities.Probability.MomentMeasure.variationalFunctional dx μ (φ j)) atTop (𝓝 (S : EReal)) ∧
      ∀ ψ : E → EReal, FunctionalInequalities.Analysis.ConvexPotential ψ → FunctionalInequalities.Probability.MomentMeasure.PotentialIntegrable ψ μ →
        (∀ x, 0 ≤ ψ x) → ψ 0 = 0 → FunctionalInequalities.Probability.MomentMeasure.variationalFunctional dx μ ψ ≤ (S : EReal) := by
  classical
  let N : Set ℝ := {r | ∃ φ : E → EReal,
    FunctionalInequalities.Analysis.ConvexPotential φ ∧ FunctionalInequalities.Probability.MomentMeasure.PotentialIntegrable φ μ ∧ (∀ x, 0 ≤ φ x) ∧ φ 0 = 0 ∧
      FunctionalInequalities.Probability.MomentMeasure.variationalFunctional dx μ φ = (r : EReal)}
  obtain ⟨hNormConv, hNormPot, L, hL⟩ := FunctionalInequalities.Probability.MomentMeasure.norm_baseline_finite dx μ hfirst
  have hN : N.Nonempty := ⟨L, (fun x : E => (‖x‖ : EReal)), hNormConv, hNormPot,
    (fun x => EReal.coe_nonneg.mpr (norm_nonneg x)), (by simp), hL⟩
  obtain ⟨U, hU⟩ := FunctionalInequalities.KLS.CEK.exists_uniform_functional_upper_readable dx μ hsub hfirst hbar
  have hNb : BddAbove N := by
    refine ⟨U, ?_⟩
    rintro r ⟨φ, _hc, hp, _hnn, _hzero, hr⟩
    have h := hU φ hp
    rw [hr] at h
    exact EReal.coe_le_coe_iff.mp h
  obtain ⟨u, _huMono, huT, huN⟩ := exists_seq_tendsto_sSup hN hNb
  have hw : ∀ j, ∃ φ : E → EReal,
      FunctionalInequalities.Analysis.ConvexPotential φ ∧ FunctionalInequalities.Probability.MomentMeasure.PotentialIntegrable φ μ ∧ (∀ x, 0 ≤ φ x) ∧ φ 0 = 0 ∧
        FunctionalInequalities.Probability.MomentMeasure.variationalFunctional dx μ φ = (u j : EReal) := huN
  choose φ hconv hpot hnn hzero hval using hw
  refine ⟨sSup N, φ, hconv, hpot, hnn, hzero, ?_, ?_⟩
  · simpa only [hval] using EReal.tendsto_coe.mpr huT
  · intro ψ hc hp hnonneg hz
    by_cases hb : FunctionalInequalities.Probability.MomentMeasure.variationalFunctional dx μ ψ = ⊥
    · rw [hb]
      exact bot_le
    have ht : FunctionalInequalities.Probability.MomentMeasure.variationalFunctional dx μ ψ ≠ ⊤ :=
      ne_of_lt ((hU ψ hp).trans_lt (EReal.coe_lt_top U))
    lift FunctionalInequalities.Probability.MomentMeasure.variationalFunctional dx μ ψ to ℝ using ⟨ht, hb⟩ with r hr
    have hrN : r ∈ N := ⟨ψ, hc, hp, hnonneg, hz, hr.symm⟩
    exact EReal.coe_le_coe_iff.mpr (le_csSup hNb hrN)
