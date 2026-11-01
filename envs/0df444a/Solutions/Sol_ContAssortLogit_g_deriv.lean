-- Prove2me | solution 1 for ContAssortLogit.g_deriv
-- status  : ACCEPTED   (prove)
-- author  : @涼宮 ハルヒ
-- created : 2026-10-31T12:20:42.37124+00:00
-- url     : https://prove2.me/submissions/0c999124-18bf-40df-93cb-f8e2437af630

import Definitions.Def_ContAssortLogit_Model
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open MeasureTheory Set Filter
open scoped Topology

private lemma tail_derivative (f : ℝ → ℝ) (hf : IntegrableOn f (Icc 0 1))
    (hc : ContinuousOn f (Ioo 0 1)) {y : ℝ} (hy : y ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (fun z => ∫ x in Icc z 1, f x) (-f y) y := by
  have hi : IntervalIntegrable f volume y 1 :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hy.2.le).mpr
      (hf.mono_set (Icc_subset_Icc hy.1.le le_rfl))
  have hd := intervalIntegral.integral_hasDerivAt_left hi
    (hc.stronglyMeasurableAtFilter isOpen_Ioo y hy)
    (hc.continuousAt (Ioo_mem_nhds hy.1 hy.2))
  apply hd.congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds hy.1 hy.2] with z hz
  rw [integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le hz.2.le]

open ContAssortLogit

theorem solution (w v : ℝ → ℝ) (vlo vhi D : ℝ) (hw : IsRevenueFn w)
    (hpar : ClassParams w vlo vhi) (hv : InClass vlo vhi D v) :
    ∀ y ∈ Ioo (0 : ℝ) 1, HasDerivAt (gfun w v) ((gfun w v y - w y) * xi v y) y := by
  intro y hy
  have hcv : ContinuousOn v (Ioo (0 : ℝ) 1) :=
    continuousOn_of_forall_continuousAt (fun x hx => (hv.2.1 x hx).1.continuousAt)
  have hcw : ContinuousOn w (Icc (0 : ℝ) 1) := hw.2.1.continuousOn
  have hcw' : ContinuousOn w (Ioo (0 : ℝ) 1) := hcw.mono Ioo_subset_Icc_self
  have hiv : IntegrableOn v (Icc (0 : ℝ) 1) := hv.2.2
  have hiwv : IntegrableOn (fun x => v x * w x) (Icc (0 : ℝ) 1) :=
    hiv.mul_continuousOn hcw isCompact_Icc
  have hdv := tail_derivative v hiv hcv hy
  have hdwv := tail_derivative (fun x => v x * w x) hiwv (hcv.mul hcw') hy
  have hnonneg : 0 ≤ ∫ x in Icc y 1, v x := by
    apply setIntegral_nonneg measurableSet_Icc
    intro x hx
    have hx01 : x ∈ Icc (0 : ℝ) 1 := ⟨hy.1.le.trans hx.1, hx.2⟩
    exact hpar.1.le.trans (hv.1 x hx01).1
  have hden : 1 + ∫ x in Icc y 1, v x ≠ 0 := by linarith
  have hd := hdwv.div (hdv.const_add 1) hden
  change HasDerivAt (fun z => (∫ x in Icc z 1, v x * w x) /
    (1 + ∫ x in Icc z 1, v x)) _ y
  apply hd.congr_deriv
  dsimp only [gfun, rev, xi]
  field_simp [hden]
  <;> ring

#print axioms solution
