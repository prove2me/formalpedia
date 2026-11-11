-- Prove2me | solution 1 for AvramDividend.Classical.avram_a06_original_cp_fixed_mark_real_moment
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T20:02:45.720783+00:00
-- url     : https://prove2.me/submissions/f49215c7-107b-4406-818c-e6d7a2afa660

import Mathlib
import Definitions.Def_levy_foundations_isCompoundPoissonDriver
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
noncomputable section

/-- Fixed-length negative-mark Laplace transform factors by i.i.d. marks. -/
theorem solution
    (P : Measure ((ℕ → ℝ) × (ℕ → ℝ)))
    [IsProbabilityMeasure P]
    (τ Y : ℕ → ((ℕ → ℝ) × (ℕ → ℝ)) → ℝ)
    (hd : LevyFoundations.IsCompoundPoissonDriver τ Y (1 : ℝ≥0)
      ((volume : Measure ℝ).restrict (Ioo (-1 : ℝ) 0)) P)
    (k : ℕ) (θ : ℝ) (hθ : 0 ≤ θ) :
    (∫ ω, Real.exp (θ * ∑ i ∈ Finset.range k, Y i ω) ∂P) =
      (∫ y, Real.exp (θ * y) ∂
        ((volume : Measure ℝ).restrict (Ioo (-1 : ℝ) 0))) ^ k := by
  have hindY : iIndepFun Y P :=
    hd.indep.precomp (g := Sum.inr) Sum.inr_injective
  have hfin : iIndepFun (fun i : Fin k => Y i.val) P :=
    hindY.precomp (g := fun i : Fin k => i.val) Fin.val_injective
  have hindE : iIndepFun
      (fun i : Fin k => fun ω => Real.exp (θ * Y i.val ω)) P := by
    exact hfin.comp (fun _ (x : ℝ) => Real.exp (θ * x))
      (fun _ => Real.measurable_exp.comp
        (measurable_const.mul measurable_id))
  have hmeas : ∀ i : Fin k,
      AEStronglyMeasurable (fun ω => Real.exp (θ * Y i.val ω)) P :=
    fun i => (Real.measurable_exp.comp
      (measurable_const.mul (hd.measurable_mark i.val))).aestronglyMeasurable
  have hprod := hindE.integral_fun_prod_eq_prod_integral hmeas
  have hpoint (ω) :
      Real.exp (θ * ∑ i ∈ Finset.range k, Y i ω) =
        ∏ i : Fin k, Real.exp (θ * Y i.val ω) := by
    rw [Finset.mul_sum, Real.exp_sum]
    exact Finset.prod_range (fun i : ℕ => Real.exp (θ * Y i ω))
  rw [show (fun ω => Real.exp (θ * ∑ i ∈ Finset.range k, Y i ω)) =
      (fun ω => ∏ i : Fin k, Real.exp (θ * Y i.val ω))
    from funext hpoint]
  rw [hprod]
  have hmark (i : Fin k) :
      (∫ ω, Real.exp (θ * Y i.val ω) ∂P) =
        ∫ y, Real.exp (θ * y) ∂
          ((volume : Measure ℝ).restrict (Ioo (-1 : ℝ) 0)) := by
    calc
      _ = ∫ y, Real.exp (θ * y) ∂Measure.map (Y i.val) P := by
        symm
        have hg : Measurable (fun y : ℝ => Real.exp (θ * y)) := by fun_prop
        exact integral_map (hd.measurable_mark i.val).aemeasurable
          hg.aestronglyMeasurable
      _ = _ := by rw [(hd.law_mark i.val).map_eq]
  simp_rw [hmark]
  simp
