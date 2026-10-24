-- Prove2me | solution 1 for FunctionalInequalities.Probability.lintegral_pi_prod_fin_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T17:58:11.88589+00:00
-- url     : https://prove2.me/submissions/4e45cc82-44c1-487e-b08e-95578ec59060

import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Probability.Independence.Integration
import Mathlib.Probability.Moments.Variance

noncomputable section
open MeasureTheory ProbabilityTheory Filter
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Probability
end FunctionalInequalities.Probability
open FunctionalInequalities FunctionalInequalities.Probability
section MeasurableSpace
variable {E : Type*}
variable [MeasurableSpace E]
namespace FunctionalInequalities.Probability
end FunctionalInequalities.Probability
open FunctionalInequalities.Probability in
/-- `∫⁻ Π_i g_i(x_i) d(⊗_i μ) = Π_i ∫⁻ g_i dμ` over `Fin N`. -/
theorem solution
    (μ : Measure E) [SigmaFinite μ] (k : ℕ) (g : Fin k → E → ENNReal)
    (hg : ∀ i, Measurable (g i)) :
    (∫⁻ x, ∏ i : Fin k, g i (x i) ∂(Measure.pi fun _ : Fin k => μ)) =
      ∏ i : Fin k, ∫⁻ x, g i x ∂μ := by
  classical
  induction k with
  | zero =>
      simp
  | succ k ih =>
      let e :=
        MeasurableEquiv.piFinSuccAbove (fun _ : Fin (k + 1) => E) 0
      let ν := Measure.pi (fun _ : Fin k => μ)
      have he :
          MeasurePreserving e
            (Measure.pi (fun _ : Fin (k + 1) => μ)) (μ.prod ν) :=
        measurePreserving_piFinSuccAbove (fun _ : Fin (k + 1) => μ) 0
      have htail :
          Measurable (fun y : Fin k → E => ∏ i : Fin k, g i.succ (y i)) := by
        apply Finset.measurable_prod
        intro i hi
        exact (hg i.succ).comp (measurable_pi_apply i)
      have hcomp :
          (fun a : E × (Fin k → E) =>
              ∏ i : Fin (k + 1), g i ((e.symm a) i)) =
            (fun a : E × (Fin k → E) =>
              g 0 a.1 * ∏ i : Fin k, g i.succ (a.2 i)) := by
        funext a
        simp [e, MeasurableEquiv.piFinSuccAbove_symm_apply,
          Fin.prod_univ_succ, Fin.insertNthEquiv, Fin.cons_zero,
          Fin.cons_succ, Fin.zero_succAbove]
      calc
        (∫⁻ x, ∏ i : Fin (k + 1), g i (x i)
            ∂Measure.pi (fun _ : Fin (k + 1) => μ)) =
            ∫⁻ a, ∏ i : Fin (k + 1), g i ((e.symm a) i) ∂(μ.prod ν) :=
          MeasurePreserving.lintegral_map_equiv
            (fun x => ∏ i : Fin (k + 1), g i (x i)) e.symm he.symm
        _ = ∫⁻ a, g 0 a.1 * ∏ i : Fin k, g i.succ (a.2 i) ∂(μ.prod ν) := by
          rw [hcomp]
        _ = (∫⁻ x, g 0 x ∂μ) *
              ∫⁻ y, ∏ i : Fin k, g i.succ (y i) ∂ν :=
          lintegral_prod_mul (hg 0).aemeasurable htail.aemeasurable
        _ = (∫⁻ x, g 0 x ∂μ) *
              ∏ i : Fin k, ∫⁻ x, g i.succ x ∂μ := by
          rw [ih (fun i => g i.succ) (fun i => hg i.succ)]
        _ = ∏ i : Fin (k + 1), ∫⁻ x, g i x ∂μ := by
          rw [Fin.prod_univ_succ]
