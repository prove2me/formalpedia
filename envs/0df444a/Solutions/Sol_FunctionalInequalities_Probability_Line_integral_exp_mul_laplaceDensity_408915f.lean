-- Prove2me | solution 1 for FunctionalInequalities.Probability.Line.integral_exp_mul_laplaceDensity_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T18:02:38.957823+00:00
-- url     : https://prove2.me/submissions/e50222e3-5572-4ea6-9b4d-089fd482f0e2

import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Line_Laplace
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Probability.Moments.MGFAnalytic

noncomputable section
open MeasureTheory
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Probability
end FunctionalInequalities.Probability
open FunctionalInequalities FunctionalInequalities.Probability
section
namespace FunctionalInequalities.Probability.Line
end FunctionalInequalities.Probability.Line
open FunctionalInequalities FunctionalInequalities.Probability FunctionalInequalities.Probability.Line
section Moments
open ProbabilityTheory Filter Set
open scoped Topology
namespace FunctionalInequalities.Probability.Line
end FunctionalInequalities.Probability.Line
open FunctionalInequalities.Probability.Line in
/-- **Local moment generating function of the Laplace law**: for `β > 0` and `|w| < β`, the
function `s ↦ e^{ws} (β/2) e^{-β|s|}` is integrable with integral `β² / (β² - w²)`. -/
theorem solution {β w : ℝ} (hβ : 0 < β) (hw : |w| < β) :
    MeasureTheory.Integrable (fun s => Real.exp (w * s) * FunctionalInequalities.Probability.Line.laplaceDensity β s) ∧
      ∫ s, Real.exp (w * s) * FunctionalInequalities.Probability.Line.laplaceDensity β s = β ^ 2 / (β ^ 2 - w ^ 2) := by
    have hw₁ : -β < w := (abs_lt.mp hw).1
    have hw₂ : w < β := (abs_lt.mp hw).2
    have hnegRate : w - β < 0 := by linarith
    have hposRate : 0 < w + β := by linarith
    have hβw : 0 < β - w := by linarith
    have hwβ : 0 < β + w := by linarith
    have hden : 0 < β ^ 2 - w ^ 2 := by
      nlinarith [mul_pos hβw hwβ]

    let f : ℝ → ℝ :=
      fun s => Real.exp (w * s) * FunctionalInequalities.Probability.Line.laplaceDensity β s

    have hpos_eq :
        ∀ s ∈ Set.Ioi (0 : ℝ),
          f s = (β / 2) * Real.exp ((w - β) * s) := by
      intro s hs
      dsimp [f, FunctionalInequalities.Probability.Line.laplaceDensity]
      rw [abs_of_pos hs]
      calc
        Real.exp (w * s) * (β / 2 * Real.exp (-(β * s))) =
            β / 2 * (Real.exp (w * s) * Real.exp (-(β * s))) := by
              ring
        _ = β / 2 * Real.exp (w * s + -(β * s)) := by
              rw [← Real.exp_add]
        _ = β / 2 * Real.exp ((w - β) * s) := by
              congr 2
              ring

    have hneg_eq :
        ∀ s ∈ Set.Iic (0 : ℝ),
          f s = (β / 2) * Real.exp ((w + β) * s) := by
      intro s hs
      dsimp [f, FunctionalInequalities.Probability.Line.laplaceDensity]
      rw [abs_of_nonpos hs]
      calc
        Real.exp (w * s) * (β / 2 * Real.exp (-(β * -s))) =
            β / 2 * (Real.exp (w * s) * Real.exp (-(β * -s))) := by
              ring
        _ = β / 2 * Real.exp (w * s + -(β * -s)) := by
              rw [← Real.exp_add]
        _ = β / 2 * Real.exp ((w + β) * s) := by
              congr 2
              ring

    have hpos_exp :
        MeasureTheory.IntegrableOn
          (fun s : ℝ => Real.exp ((w - β) * s)) (Set.Ioi 0) :=
      integrableOn_exp_mul_Ioi (a := w - β) hnegRate 0

    have hneg_exp :
        MeasureTheory.IntegrableOn
          (fun s : ℝ => Real.exp ((w + β) * s)) (Set.Iic 0) :=
      integrableOn_exp_mul_Iic (a := w + β) hposRate 0

    have hpos : MeasureTheory.IntegrableOn f (Set.Ioi 0) := by
      have h := hpos_exp.const_mul (β / 2)
      apply h.congr
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with s hs
      exact (hpos_eq s hs).symm

    have hneg : MeasureTheory.IntegrableOn f (Set.Iic 0) := by
      have h := hneg_exp.const_mul (β / 2)
      apply h.congr
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Iic] with s hs
      exact (hneg_eq s hs).symm

    have hglob : MeasureTheory.Integrable f := by
      have h := hneg.union hpos
      simpa [Set.Iic_union_Ioi] using h

    have hpos_val :
        ∫ s in Set.Ioi (0 : ℝ), f s =
          (β / 2) * (1 / (β - w)) := by
      calc
        ∫ s in Set.Ioi (0 : ℝ), f s =
            ∫ s in Set.Ioi (0 : ℝ),
              (β / 2) * Real.exp ((w - β) * s) := by
          apply MeasureTheory.integral_congr_ae
          filter_upwards
            [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with s hs
          exact hpos_eq s hs
        _ = (β / 2) *
            ∫ s in Set.Ioi (0 : ℝ), Real.exp ((w - β) * s) := by
          simpa [smul_eq_mul] using
            (MeasureTheory.integral_smul
              (μ := MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)))
              (β / 2) (fun s : ℝ => Real.exp ((w - β) * s)))
        _ = (β / 2) * (1 / (β - w)) := by
          rw [integral_exp_mul_Ioi (a := w - β) hnegRate (0 : ℝ)]
          simp only [mul_zero, Real.exp_zero]
          field_simp [ne_of_lt hnegRate]
          ring

    have hneg_val :
        ∫ s in Set.Iic (0 : ℝ), f s =
          (β / 2) * (1 / (β + w)) := by
      calc
        ∫ s in Set.Iic (0 : ℝ), f s =
            ∫ s in Set.Iic (0 : ℝ),
              (β / 2) * Real.exp ((w + β) * s) := by
          apply MeasureTheory.integral_congr_ae
          filter_upwards
            [MeasureTheory.ae_restrict_mem measurableSet_Iic] with s hs
          exact hneg_eq s hs
        _ = (β / 2) *
            ∫ s in Set.Iic (0 : ℝ), Real.exp ((w + β) * s) := by
          simpa [smul_eq_mul] using
            (MeasureTheory.integral_smul
              (μ := MeasureTheory.volume.restrict (Set.Iic (0 : ℝ)))
              (β / 2) (fun s : ℝ => Real.exp ((w + β) * s)))
        _ = (β / 2) * (1 / (β + w)) := by
          rw [integral_exp_mul_Iic (a := w + β) hposRate (0 : ℝ)]
          simp only [mul_zero, Real.exp_zero]
          field_simp [ne_of_gt hposRate]
          ring

    refine ⟨?_, ?_⟩
    · simpa [f] using hglob
    · change ∫ s, f s = β ^ 2 / (β ^ 2 - w ^ 2)
      have hsplit :=
        MeasureTheory.integral_add_compl
          (μ := MeasureTheory.volume) (s := Set.Iic (0 : ℝ))
          measurableSet_Iic hglob
      rw [← hsplit, Set.compl_Iic, hneg_val, hpos_val]
      field_simp [ne_of_gt hβw, ne_of_gt hwβ, ne_of_gt hden]
      ring
