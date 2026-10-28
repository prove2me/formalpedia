-- Prove2me | solution 1 for FunctionalInequalities.Probability.integrable_exp_sub_norm_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T13:38:28.246555+00:00
-- url     : https://prove2.me/submissions/db1c6555-be62-4fce-998e-25741ebe6b15

import Definitions.Def_KLSModular_FunctionalInequalities_Probability_MomentMeasure_ConjugateMass

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
/-- Actual exponential norm decay is Haar-integrable in every finite dimension.
The nontrivial case uses polar integration; the zero-dimensional case is compact. -/
theorem solution [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (dx : Measure E) [dx.IsAddHaarMeasure] {c : ℝ} (hc : 0 < c) (M : ℝ) :
    Integrable (fun y : E => Real.exp (M - c * ‖y‖)) dx := by
  rcases subsingleton_or_nontrivial E with hE | hE
  · let := hE
    have : CompactSpace E := inferInstance
    have : IsFiniteMeasure dx := inferInstance
    have heq : (fun y : E => Real.exp (M - c * ‖y‖)) = fun _ : E => Real.exp M := by
      funext y
      rw [Subsingleton.elim y 0]
      simp
    rw [heq]
    exact integrable_const _
  · let := hE
    have hi : Integrable (fun y : E => Real.exp (-c * ‖y‖)) dx := by
      apply (integrable_fun_norm_addHaar dx (f := fun t : ℝ => Real.exp (-c * t))).mpr
      simpa only [smul_eq_mul, Real.rpow_natCast, Real.rpow_one] using
        (integrableOn_rpow_mul_exp_neg_mul_rpow
          (s := ((Module.finrank ℝ E - 1 : ℕ) : ℝ)) (p := 1)
          (by have hsn := Nat.cast_nonneg (α := ℝ) (Module.finrank ℝ E - 1); linarith) (by norm_num) hc)
    convert hi.const_mul (Real.exp M) using 1
    funext y
    rw [← Real.exp_add]
    congr 1
    ring
