-- Prove2me | solution 1 for ContAssortLogit.eq_27
-- status  : ACCEPTED   (prove)
-- author  : @涼宮 ハルヒ
-- created : 2026-11-02T12:22:53.320241+00:00
-- url     : https://prove2.me/submissions/a7e0c7ea-07b4-4fba-8d63-b9f675695568

import Definitions.Def_ContAssortLogit_Model
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

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

private lemma g_derivative (w v : ℝ → ℝ) (vlo vhi D : ℝ) (hw : IsRevenueFn w)
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


theorem solution (w v : ℝ → ℝ) (vlo vhi D : ℝ) (hw : IsRevenueFn w)
    (hpar : ClassParams w vlo vhi) (hv : InClass vlo vhi D v) (Mw : ℝ)
    (hMw : ∀ x ∈ Icc (0 : ℝ) 1, derivWithin w (Icc 0 1) x ≤ Mw) :
    ∀ y ∈ Ioo (0 : ℝ) 1, ∃ g2 : ℝ, HasDerivAt (deriv (gfun w v)) g2 y ∧
      -g2 ≤ D + 2 * vhi ^ 2 + Mw * vhi := by
  intro y hy
  have hycc : y ∈ Icc (0 : ℝ) 1 := ⟨hy.1.le, hy.2.le⟩
  have hsub : Icc y 1 ⊆ Icc (0 : ℝ) 1 := Icc_subset_Icc hy.1.le le_rfl
  have hcv : ContinuousOn v (Ioo (0 : ℝ) 1) :=
    continuousOn_of_forall_continuousAt (fun z hz => (hv.2.1 z hz).1.continuousAt)
  have hcw : ContinuousOn w (Icc (0 : ℝ) 1) := hw.2.1.continuousOn
  have hiv : IntegrableOn v (Icc (0 : ℝ) 1) := hv.2.2
  have hiwv : IntegrableOn (fun z => v z * w z) (Icc (0 : ℝ) 1) :=
    hiv.mul_continuousOn hcw isCompact_Icc
  have hv0 (z : ℝ) (hz : z ∈ Icc (0 : ℝ) 1) : 0 ≤ v z :=
    hpar.1.le.trans (hv.1 z hz).1
  have hI0 : 0 ≤ ∫ z in Icc y 1, v z :=
    setIntegral_nonneg measurableSet_Icc (fun z hz => hv0 z (hsub hz))
  have hA1 : 1 ≤ 1 + ∫ z in Icc y 1, v z := by linarith
  have hApos : 0 < 1 + ∫ z in Icc y 1, v z := by linarith
  have hA : 1 + ∫ z in Icc y 1, v z ≠ 0 := hApos.ne'
  have hN0 : 0 ≤ ∫ z in Icc y 1, v z * w z :=
    setIntegral_nonneg measurableSet_Icc (fun z hz =>
      mul_nonneg (hv0 z (hsub hz)) (hw.1 (hsub hz)).1)
  have hNle : (∫ z in Icc y 1, v z * w z) ≤ ∫ z in Icc y 1, v z := by
    apply setIntegral_mono_on (hiwv.mono_set hsub) (hiv.mono_set hsub) measurableSet_Icc
    intro z hz
    exact mul_le_of_le_one_right (hv0 z (hsub hz)) (hw.1 (hsub hz)).2
  have hg0 : 0 ≤ gfun w v y := by
    dsimp only [gfun, rev]
    exact div_nonneg hN0 hApos.le
  have hg1 : gfun w v y ≤ 1 := by
    dsimp only [gfun, rev]
    apply (div_le_one hApos).mpr
    linarith
  have hxi0 : 0 ≤ xi v y := div_nonneg (hv0 y hycc) hApos.le
  have hvhi0 : 0 ≤ vhi := hpar.1.le.trans hpar.2.1.le
  have hxi1 : xi v y ≤ vhi := by
    apply (div_le_iff₀ hApos).mpr
    nlinarith [(hv.1 y hycc).2, mul_nonneg hvhi0 hI0]
  have hxi2 : (xi v y) ^ 2 ≤ vhi ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hxi1) (add_nonneg hvhi0 hxi0)]
  have hD0 : 0 ≤ D := (abs_nonneg _).trans (hv.2.1 y hy).2
  have hdvbound : |deriv v y / (1 + ∫ z in Icc y 1, v z)| ≤ D := by
    rw [abs_div, abs_of_pos hApos]
    apply (div_le_iff₀ hApos).mpr
    nlinarith [(hv.2.1 y hy).2, mul_nonneg hD0 hI0]
  have hgw : |gfun w v y - w y| ≤ 1 := by
    apply abs_le.mpr
    constructor <;> linarith [(hw.1 hycc).1, (hw.1 hycc).2]
  have hwdif : DifferentiableAt ℝ w y :=
    (hw.2.1.differentiableOn_one y hycc).differentiableAt (Icc_mem_nhds hy.1 hy.2)
  have hwdw : derivWithin w (Icc 0 1) y = deriv w y :=
    derivWithin_of_mem_nhds (Icc_mem_nhds hy.1 hy.2)
  have hwbound : deriv w y ≤ Mw := by simpa only [hwdw] using hMw y hycc
  have hw0 : 0 ≤ deriv w y := by
    obtain ⟨k, hk, hkw⟩ := hw.2.2
    have hh := hkw y hycc
    rw [hwdw] at hh
    linarith
  have hMw0 : 0 ≤ Mw := hw0.trans hwbound
  have htail := tail_derivative v hiv hcv hy
  have hxider : HasDerivAt (xi v)
      (deriv v y / (1 + ∫ z in Icc y 1, v z) + (xi v y) ^ 2) y := by
    have hd := (hv.2.1 y hy).1.hasDerivAt.div (htail.const_add 1) hA
    apply hd.congr_deriv
    dsimp only [xi]
    field_simp [hA]
    <;> ring
  have hgder := g_derivative w v vlo vhi D hw hpar hv y hy
  let g2 : ℝ := (gfun w v y - w y) *
      (deriv v y / (1 + ∫ z in Icc y 1, v z) + 2 * (xi v y) ^ 2) - deriv w y * xi v y
  have hg2formula : HasDerivAt (fun z => (gfun w v z - w z) * xi v z) g2 y := by
    have hh := ((hgder.sub hwdif.hasDerivAt).mul hxider)
    apply hh.congr_deriv
    dsimp only [g2, Pi.sub_apply]
    ring
  have hderivEq : deriv (gfun w v) =ᶠ[𝓝 y] (fun z => (gfun w v z - w z) * xi v z) := by
    filter_upwards [Ioo_mem_nhds hy.1 hy.2] with z hz
    exact (g_derivative w v vlo vhi D hw hpar hv z hz).deriv
  refine ⟨g2, hg2formula.congr_of_eventuallyEq hderivEq, ?_⟩
  have hB : |deriv v y / (1 + ∫ z in Icc y 1, v z) + 2 * (xi v y) ^ 2| ≤
      D + 2 * vhi ^ 2 := by
    calc
      _ ≤ |deriv v y / (1 + ∫ z in Icc y 1, v z)| + |2 * (xi v y) ^ 2| := abs_add_le _ _
      _ = |deriv v y / (1 + ∫ z in Icc y 1, v z)| + 2 * (xi v y) ^ 2 := by
        rw [abs_of_nonneg (by positivity : 0 ≤ 2 * (xi v y) ^ 2)]
      _ ≤ D + 2 * vhi ^ 2 := by linarith
  have hprod : -(gfun w v y - w y) *
      (deriv v y / (1 + ∫ z in Icc y 1, v z) + 2 * (xi v y) ^ 2) ≤ D + 2 * vhi ^ 2 := by
    calc
      _ = -((gfun w v y - w y) *
          (deriv v y / (1 + ∫ z in Icc y 1, v z) + 2 * (xi v y) ^ 2)) := by ring
      _ ≤ |(gfun w v y - w y) *
          (deriv v y / (1 + ∫ z in Icc y 1, v z) + 2 * (xi v y) ^ 2)| := neg_le_abs _
      _ = |gfun w v y - w y| *
          |deriv v y / (1 + ∫ z in Icc y 1, v z) + 2 * (xi v y) ^ 2| := abs_mul _ _
      _ ≤ 1 * (D + 2 * vhi ^ 2) :=
        mul_le_mul hgw hB (abs_nonneg _) (by positivity)
      _ = D + 2 * vhi ^ 2 := one_mul _
  have hwprod : deriv w y * xi v y ≤ Mw * vhi :=
    (mul_le_mul_of_nonneg_right hwbound hxi0).trans (mul_le_mul_of_nonneg_left hxi1 hMw0)
  dsimp only [g2]
  nlinarith
#print axioms solution
