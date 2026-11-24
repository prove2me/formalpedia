-- Prove2me | solution 1 for DimdPolyLEAN.circleChar_carrierArc_arcParam
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:47:40.915722+00:00
-- url     : https://prove2.me/submissions/639de467-45fa-4137-81dc-55765ac892c8

module
public import Mathlib.Analysis.Normed.Lp.SmoothApprox
public import Mathlib.Analysis.Fourier.FourierTransform
public import Mathlib.MeasureTheory.Function.Holder
public import Mathlib.MeasureTheory.Function.LpSpace.DomAct.Basic
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Definitions
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Definitions.Def_LeanPool_PhaseRetrieval_Constant_Internal_RotationalAveraging
public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
public import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
public import Mathlib.MeasureTheory.Function.LpSpace.DomAct.Continuous
public import Mathlib.MeasureTheory.Measure.RegularityCompacts
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_ImportedAnalyticInputs
public import Theorems.Thm_DimdPolyLEAN_circleChar_mk

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open DimdPolyLEAN
open MeasureTheory Filter
open scoped ENNReal Topology RealInnerProductSpace
namespace DimdPolyLEAN
theorem _root_.solution {N : Nat} (k : Fin N) (t : ℝ) :
    circleChar N (arcParam (carrierArc N k) t) =
      Complex.exp (Complex.I * (2 * Real.pi * t)) := by
  rw [arcParam, circleChar_mk]
  unfold carrierArc arcLength
  have hN : (N : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt k.pos)
  have hNreal : (N : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt k.pos)
  have harg :
      Complex.I * (N : ℂ) *
          ↑((2 * Real.pi) * (k.1 : ℝ) / (N : ℝ) +
            t * ((2 * Real.pi) * ((k.1 + 1 : Nat) : ℝ) / (N : ℝ) -
              (2 * Real.pi) * (k.1 : ℝ) / (N : ℝ))) =
        Complex.I * (2 * Real.pi * (k.1 : ℝ)) +
          Complex.I * (2 * Real.pi * t) := by
    push_cast
    field_simp [hN, hNreal]
    ring
  rw [harg, Complex.exp_add]
  have hint : Complex.exp (Complex.I * (2 * Real.pi * (k.1 : ℝ))) = 1 := by
    rw [show Complex.I * (2 * Real.pi * (k.1 : ℝ)) =
        (k.1 : ℂ) * (2 * Real.pi * Complex.I) by
      push_cast
      ring]
    exact Complex.exp_nat_mul_two_pi_mul_I k.1
  rw [hint, one_mul]
end DimdPolyLEAN
