-- Prove2me | solution 1 for FunctionalInequalities.Probability.MomentMeasure.log_sub_ge_of_integral_limits_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T13:38:55.088975+00:00
-- url     : https://prove2.me/submissions/5d45a041-45de-4087-9d07-7ec526467244

import Definitions.Def_KLSModular_FunctionalInequalities_Probability_MomentMeasure_ConjugateMass

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology
open FunctionalInequalities.Analysis
section
set_option autoImplicit false
set_option relaxedAutoImplicit false
open Filter
/-- CEK Proposition12 limit assembly: the actual extended logarithm and real
integral limits produce the functional comparison. Neither positive finite
sequence mass nor log convergence nor the final comparison is assumed.
Zero/infinite masses at a finite prefix remain allowed. This is an assembly
helper for the two actual Lemma17 inequalities, not an attainment theorem. -/
theorem solution
    (a : ℕ → ℝ≥0∞) (m : ℕ → ℝ) (Z : ℝ≥0∞) (r S M : ℝ)
    (hnn : ∀ j, 0 ≤ m j)
    (hF : Tendsto (fun j => ENNReal.log (a j) - (m j : EReal)) atTop (𝓝 (S : EReal)))
    (hm : Tendsto m atTop (𝓝 M))
    (hfirst : ENNReal.ofReal r ≤ liminf (fun j => ENNReal.ofReal (m j)) atTop)
    (hsecond : limsup a atTop ≤ Z) :
    0 < Z ∧ (S : EReal) ≤ ENNReal.log Z - (r : EReal) := by
  have hmE : Tendsto (fun j => (m j : EReal)) atTop (𝓝 (M : EReal)) :=
    EReal.tendsto_coe.mpr hm
  have hlog : Tendsto (fun j => ENNReal.log (a j)) atTop (𝓝 ((S + M : ℝ) : EReal)) := by
    have h := (EReal.continuousAt_add_coe_coe S M).tendsto.comp (hF.prodMk_nhds hmE)
    simpa only [Function.comp_def, EReal.sub_add_cancel, ← EReal.coe_add] using h
  have ha : Tendsto a atTop (𝓝 (ENNReal.ofReal (Real.exp (S + M)))) := by
    have h := (ENNReal.continuous_exp.tendsto ((S + M : ℝ) : EReal)).comp hlog
    simpa only [Function.comp_def, ENNReal.exp_log, EReal.exp_coe] using h
  have hZ : ENNReal.ofReal (Real.exp (S + M)) ≤ Z := by
    simpa only [ha.limsup_eq] using hsecond
  have hmR : Tendsto (fun j => ENNReal.ofReal (m j)) atTop (𝓝 (ENNReal.ofReal M)) :=
    (ENNReal.continuous_ofReal.tendsto M).comp hm
  have hM : 0 ≤ M := ge_of_tendsto hm (Eventually.of_forall hnn)
  have hrM : r ≤ M := (ENNReal.ofReal_le_ofReal_iff hM).mp (by
    simpa only [hmR.liminf_eq] using hfirst)
  have hl : ((S + M : ℝ) : EReal) ≤ ENNReal.log Z := by
    have h := ENNReal.log_le_log hZ
    simpa only [ENNReal.log_ofReal_of_pos (Real.exp_pos _), Real.log_exp] using h
  refine ⟨(ENNReal.ofReal_pos.mpr (Real.exp_pos _)).trans_le hZ, ?_⟩
  calc
    (S : EReal) ≤ ((S + M - r : ℝ) : EReal) := EReal.coe_le_coe_iff.mpr (by linarith)
    _ = ((S + M : ℝ) : EReal) - (r : EReal) := EReal.coe_sub _ _
    _ ≤ _ := EReal.sub_le_sub hl le_rfl
