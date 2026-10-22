-- Prove2me | solution 1 for AvramDividend.Classical.chat06_laplace_random_mark_sum_of_indep_count
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-21T11:22:00.064607+00:00
-- url     : https://prove2.me/submissions/1f1de0e7-da47-4f2d-bc62-7d08112e619e

import Mathlib.Probability.HasLaw
import Mathlib.Probability.Distributions.Poisson.Basic
import Mathlib.Probability.Independence.Integration
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic.FunProp

/-!
Adapted in part from the independent-count conditioning method of
LeanLevy Contributors, LeanLevy/Processes/CompoundPoissonLaw.lean.
MIT licence: https://github.com/slink/LeanLevy/blob/main/LICENSE
This is a separate real-Laplace argument for negative marks.
-/

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set Real
open scoped NNReal ENNReal

namespace AvramChat06
/-- Countable disintegration of the Laplace transform of a marked
Poisson sum. Finite-mark independence and the Poisson generating
series are explicit hypotheses, so no unpublished helper import is used. -/
theorem laplace_random_mark_sum_of_indep_count
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (N : Ω → ℕ) (Y : ℕ → Ω → ℝ)
    (hN : Measurable N) (hY : ∀ n, Measurable (Y n))
    (hNY : IndepFun N (fun ω n => Y n ω) P)
    (r : ℝ≥0) (hLaw : HasLaw N (poissonMeasure r) P)
    (θ m : ℝ)
    (hFint : Integrable (fun ω =>
      Real.exp (θ * ∑ j ∈ Finset.range (N ω), Y j ω)) P)
    (hMarks : ∀ k, (∫ ω,
      Real.exp (θ * ∑ j ∈ Finset.range k, Y j ω) ∂P) = m ^ k)
    (hPGF : (∫ n : ℕ, m ^ n ∂poissonMeasure r) =
      Real.exp ((r : ℝ) * (m - 1))) :
    (∫ ω, Real.exp (θ * ∑ j ∈ Finset.range (N ω), Y j ω) ∂P) =
      Real.exp ((r : ℝ) * (m - 1)) := by
  classical
  let F : Ω → ℝ :=
    fun ω => Real.exp (θ * ∑ j ∈ Finset.range (N ω), Y j ω)
  let s : ℕ → Set Ω := fun k => {ω | N ω = k}
  have hs_meas : ∀ k, MeasurableSet (s k) :=
    fun k => hN (measurableSet_singleton k)
  have hs_disj : Pairwise (fun i j => Disjoint (s i) (s j)) := by
    intro k k' hkk'
    simp only [Set.disjoint_left, s, Set.mem_setOf_eq]
    intro ω h1 h2
    exact hkk' (h1.symm.trans h2)
  have hunion : (⋃ k, s k) = Set.univ :=
    Set.eq_univ_of_forall fun ω => Set.mem_iUnion.2 ⟨N ω, rfl⟩
  have hpart := hasSum_integral_iUnion hs_meas hs_disj
    (by rw [hunion]; exact hFint.integrableOn)
  rw [hunion, setIntegral_univ] at hpart
  have hYbar_ae : AEMeasurable (fun ω n => Y n ω) P :=
    (measurable_pi_lambda _ hY).aemeasurable
  have hterm (k : ℕ) :
      (∫ ω in s k, F ω ∂P) =
        (poissonMeasure r).real {k} * m ^ k := by
    have hFcong : Set.EqOn F
        (fun ω => Real.exp (θ * ∑ j ∈ Finset.range k, Y j ω))
        (s k) := by
      intro ω hk
      change N ω = k at hk
      simp [F, hk]
    have hG :
        (s k).indicator
          (fun ω => Real.exp (θ * ∑ j ∈ Finset.range k, Y j ω)) =
        (fun ω => (if N ω = k then (1 : ℝ) else 0) *
          Real.exp (θ * ∑ j ∈ Finset.range k, Y j ω)) := by
      funext ω
      simp only [Set.indicator_apply, s, Set.mem_setOf_eq]
      by_cases h : N ω = k <;> simp [h]
    have hfmeas : AEStronglyMeasurable
        (fun n : ℕ => if n = k then (1 : ℝ) else 0) (P.map N) :=
      (measurable_of_countable _).aestronglyMeasurable
    have hgmeas : AEStronglyMeasurable
        (fun y : ℕ → ℝ =>
          Real.exp (θ * ∑ j ∈ Finset.range k, y j))
          (P.map (fun ω n => Y n ω)) := by
      have h : Measurable (fun y : ℕ → ℝ =>
          Real.exp (θ * ∑ j ∈ Finset.range k, y j)) := by
        fun_prop
      exact h.aestronglyMeasurable
    have hprod :
        (∫ ω, (if N ω = k then (1 : ℝ) else 0) *
          Real.exp (θ * ∑ j ∈ Finset.range k, Y j ω) ∂P) =
        (∫ ω, if N ω = k then (1 : ℝ) else 0 ∂P) *
        ∫ ω, Real.exp (θ * ∑ j ∈ Finset.range k, Y j ω) ∂P :=
      hNY.integral_fun_comp_mul_comp
        (f := fun n : ℕ => if n = k then (1 : ℝ) else 0)
        (g := fun y : ℕ → ℝ =>
          Real.exp (θ * ∑ j ∈ Finset.range k, y j))
        hN.aemeasurable hYbar_ae hfmeas hgmeas
    have hμreal : P.real (s k) = (poissonMeasure r).real {k} := by
      have heq : P (s k) = poissonMeasure r {k} := by
        rw [show s k = N ⁻¹' {k} from rfl,
          ← Measure.map_apply hN (measurableSet_singleton k), hLaw.map_eq]
      rw [measureReal_def, heq, ← measureReal_def]
    have hfint : (∫ ω, if N ω = k then (1 : ℝ) else 0 ∂P) =
        (poissonMeasure r).real {k} := by
      have heq :
          (fun ω => if N ω = k then (1 : ℝ) else 0) =
          (s k).indicator fun _ => (1 : ℝ) := by
        funext ω
        simp only [Set.indicator_apply, s, Set.mem_setOf_eq]
      rw [heq, integral_indicator_const (1 : ℝ) (hs_meas k), hμreal]
      simp
    rw [setIntegral_congr_fun (hs_meas k) hFcong,
      ← integral_indicator (hs_meas k), hG, hprod, hfint, hMarks]
  have hSum : HasSum
      (fun k : ℕ => (poissonMeasure r).real {k} * m ^ k)
      (∫ ω, F ω ∂P) := by
    have hf : (fun k => ∫ ω in s k, F ω ∂P) =
        (fun k => (poissonMeasure r).real {k} * m ^ k) :=
      funext hterm
    rwa [hf] at hpart
  rw [← hSum.tsum_eq]
  have hpoisson : (∑' k : ℕ,
      (poissonMeasure r).real {k} * m ^ k) =
      ∫ k : ℕ, m ^ k ∂poissonMeasure r := by
    rw [integral_poissonMeasure]
    simp only [smul_eq_mul]
    simp_rw [poissonMeasure_real_singleton]
  exact hpoisson.trans hPGF
end AvramChat06
open AvramChat06
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (N : Ω → ℕ) (Y : ℕ → Ω → ℝ)
    (hN : Measurable N) (hY : ∀ n, Measurable (Y n))
    (hNY : IndepFun N (fun ω n => Y n ω) P)
    (r : ℝ≥0) (hLaw : HasLaw N (poissonMeasure r) P)
    (θ m : ℝ)
    (hFint : Integrable (fun ω =>
      Real.exp (θ * ∑ j ∈ Finset.range (N ω), Y j ω)) P)
    (hMarks : ∀ k, (∫ ω,
      Real.exp (θ * ∑ j ∈ Finset.range k, Y j ω) ∂P) = m ^ k)
    (hPGF : (∫ n : ℕ, m ^ n ∂poissonMeasure r) =
      Real.exp ((r : ℝ) * (m - 1))) :
    (∫ ω, Real.exp (θ * ∑ j ∈ Finset.range (N ω), Y j ω) ∂P) =
      Real.exp ((r : ℝ) * (m - 1)) := by
  exact laplace_random_mark_sum_of_indep_count P N Y hN hY
    hNY r hLaw θ m hFint hMarks hPGF
