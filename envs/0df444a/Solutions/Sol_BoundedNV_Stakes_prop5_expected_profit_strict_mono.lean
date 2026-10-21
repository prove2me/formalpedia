-- Prove2me | solution 1 for BoundedNV.Stakes.prop5_expected_profit_strict_mono
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T00:29:56.92671+00:00
-- url     : https://prove2.me/submissions/1d20eb94-d279-4d0f-aa99-0e2f41ac058f

import Mathlib
import Definitions.Def_BoundedNV_ExpFam_Logit
set_option autoImplicit false
open MeasureTheory

/-- weighted Chebyshev-type core: integral over the product of the symmetrized integrand. -/
theorem BNS_cheb_core (μ : Measure ℝ) [SFinite μ] (g w1 w2 : ℝ → ℝ)
    (hw1 : Integrable w1 μ) (hw2 : Integrable w2 μ)
    (hg1 : Integrable (fun x => g x * w1 x) μ) (hg2 : Integrable (fun x => g x * w2 x) μ) :
    ∫ z : ℝ × ℝ, (g z.1 - g z.2) * (w1 z.1 * w2 z.2 - w1 z.2 * w2 z.1) ∂(μ.prod μ) =
      2 * ((∫ x, g x * w1 x ∂μ) * (∫ x, w2 x ∂μ) - (∫ x, g x * w2 x ∂μ) * (∫ x, w1 x ∂μ)) ∧
    Integrable (fun z : ℝ × ℝ => (g z.1 - g z.2) * (w1 z.1 * w2 z.2 - w1 z.2 * w2 z.1)) (μ.prod μ) := by
  have e : (fun z : ℝ × ℝ => (g z.1 - g z.2) * (w1 z.1 * w2 z.2 - w1 z.2 * w2 z.1)) =
      fun z => ((g z.1 * w1 z.1) * w2 z.2 - (g z.1 * w2 z.1) * w1 z.2) +
        (-(w1 z.1 * (g z.2 * w2 z.2)) + w2 z.1 * (g z.2 * w1 z.2)) := by
    funext z; ring
  have i1 : Integrable (fun z : ℝ × ℝ => (g z.1 * w1 z.1) * w2 z.2) (μ.prod μ) := hg1.mul_prod hw2
  have i2 : Integrable (fun z : ℝ × ℝ => (g z.1 * w2 z.1) * w1 z.2) (μ.prod μ) := hg2.mul_prod hw1
  have i3 : Integrable (fun z : ℝ × ℝ => w1 z.1 * (g z.2 * w2 z.2)) (μ.prod μ) := hw1.mul_prod hg2
  have i4 : Integrable (fun z : ℝ × ℝ => w2 z.1 * (g z.2 * w1 z.2)) (μ.prod μ) := hw2.mul_prod hg1
  have i12 : Integrable (fun z : ℝ × ℝ => (g z.1 * w1 z.1) * w2 z.2 - (g z.1 * w2 z.1) * w1 z.2)
      (μ.prod μ) := i1.sub i2
  have i34 : Integrable (fun z : ℝ × ℝ => -(w1 z.1 * (g z.2 * w2 z.2)) + w2 z.1 * (g z.2 * w1 z.2))
      (μ.prod μ) := i3.neg.add i4
  have i3n : Integrable (fun z : ℝ × ℝ => -(w1 z.1 * (g z.2 * w2 z.2))) (μ.prod μ) := i3.neg
  rw [e]
  refine ⟨?_, i12.add i34⟩
  have p1 : ∫ z : ℝ × ℝ, (g z.1 * w1 z.1) * w2 z.2 ∂(μ.prod μ) =
      (∫ x, g x * w1 x ∂μ) * ∫ x, w2 x ∂μ := integral_prod_mul (fun x => g x * w1 x) w2
  have p2 : ∫ z : ℝ × ℝ, (g z.1 * w2 z.1) * w1 z.2 ∂(μ.prod μ) =
      (∫ x, g x * w2 x ∂μ) * ∫ x, w1 x ∂μ := integral_prod_mul (fun x => g x * w2 x) w1
  have p3 : ∫ z : ℝ × ℝ, w1 z.1 * (g z.2 * w2 z.2) ∂(μ.prod μ) =
      (∫ x, w1 x ∂μ) * ∫ x, g x * w2 x ∂μ := integral_prod_mul w1 (fun x => g x * w2 x)
  have p4 : ∫ z : ℝ × ℝ, w2 z.1 * (g z.2 * w1 z.2) ∂(μ.prod μ) =
      (∫ x, w2 x ∂μ) * ∫ x, g x * w1 x ∂μ := integral_prod_mul w2 (fun x => g x * w1 x)
  rw [integral_add i12 i34, integral_sub i1 i2, integral_add i3n i4,
    integral_neg, p1, p2, p3, p4]
  ring

theorem BNS_pt (π g : ℝ → ℝ) (t1 t2 : ℝ) (ht : t2 < t1)
    (hg : ∀ x y, π x ≤ π y → g x ≤ g y) (x y : ℝ) :
    0 ≤ (g x - g y) * (Real.exp (t1 * π x) * Real.exp (t2 * π y) -
      Real.exp (t1 * π y) * Real.exp (t2 * π x)) := by
  rw [← Real.exp_add, ← Real.exp_add]
  rcases le_total (π x) (π y) with h | h
  · have h1 := hg x y h
    have h2 : Real.exp (t1 * π x + t2 * π y) ≤ Real.exp (t1 * π y + t2 * π x) :=
      Real.exp_le_exp.2 (by nlinarith)
    exact mul_nonneg_of_nonpos_of_nonpos (by linarith) (by linarith)
  · have h1 := hg y x h
    have h2 : Real.exp (t1 * π y + t2 * π x) ≤ Real.exp (t1 * π x + t2 * π y) :=
      Real.exp_le_exp.2 (by nlinarith)
    exact mul_nonneg (by linarith) (by linarith)

theorem BNS_pt_strict (π : ℝ → ℝ) (t1 t2 : ℝ) (ht : t2 < t1) (x y : ℝ) (hxy : π x ≠ π y) :
    0 < (π x - π y) * (Real.exp (t1 * π x) * Real.exp (t2 * π y) -
      Real.exp (t1 * π y) * Real.exp (t2 * π x)) := by
  rw [← Real.exp_add, ← Real.exp_add]
  rcases lt_or_gt_of_ne hxy with h | h
  · have h2 : Real.exp (t1 * π x + t2 * π y) < Real.exp (t1 * π y + t2 * π x) :=
      Real.exp_lt_exp.2 (by nlinarith)
    exact mul_pos_of_neg_of_neg (by linarith) (by linarith)
  · have h2 : Real.exp (t1 * π y + t2 * π x) < Real.exp (t1 * π x + t2 * π y) :=
      Real.exp_lt_exp.2 (by nlinarith)
    exact mul_pos (by linarith) (by linarith)

theorem BNS_cheb (μ : Measure ℝ) [SFinite μ] (π g : ℝ → ℝ) (t1 t2 : ℝ) (ht : t2 < t1)
    (hπ : Measurable π) (hgm : Measurable g)
    (hg : ∀ x y, π x ≤ π y → g x ≤ g y)
    (hw1 : Integrable (fun x => Real.exp (t1 * π x)) μ) (hw2 : Integrable (fun x => Real.exp (t2 * π x)) μ)
    (hg1 : Integrable (fun x => g x * Real.exp (t1 * π x)) μ)
    (hg2 : Integrable (fun x => g x * Real.exp (t2 * π x)) μ) :
    (∫ x, g x * Real.exp (t2 * π x) ∂μ) * (∫ x, Real.exp (t1 * π x) ∂μ) ≤
      (∫ x, g x * Real.exp (t1 * π x) ∂μ) * (∫ x, Real.exp (t2 * π x) ∂μ) := by
  obtain ⟨h1, h2⟩ := BNS_cheb_core μ g _ _ hw1 hw2 hg1 hg2
  have hnn : 0 ≤ ∫ z : ℝ × ℝ, (g z.1 - g z.2) * (Real.exp (t1 * π z.1) * Real.exp (t2 * π z.2) -
      Real.exp (t1 * π z.2) * Real.exp (t2 * π z.1)) ∂(μ.prod μ) := by
    refine integral_nonneg fun z => ?_
    exact BNS_pt π g t1 t2 ht hg z.1 z.2
  linarith


theorem BNS_e1 (lam β : ℝ) (π : ℝ → ℝ) (x : ℝ) :
    Real.exp (lam * π x / β) = Real.exp ((lam / β) * π x) := by
  congr 1; ring

theorem BNS_strict (μ : Measure ℝ) [SFinite μ] (π : ℝ → ℝ) (t1 t2 : ℝ) (ht : t2 < t1)
    (hw1 : Integrable (fun x => Real.exp (t1 * π x)) μ)
    (hw2 : Integrable (fun x => Real.exp (t2 * π x)) μ)
    (hg1 : Integrable (fun x => π x * Real.exp (t1 * π x)) μ)
    (hg2 : Integrable (fun x => π x * Real.exp (t2 * π x)) μ)
    (hnc : ¬ ∃ k : ℝ, ∀ᵐ x ∂μ, π x = k) :
    (∫ x, π x * Real.exp (t2 * π x) ∂μ) * (∫ x, Real.exp (t1 * π x) ∂μ) <
      (∫ x, π x * Real.exp (t1 * π x) ∂μ) * (∫ x, Real.exp (t2 * π x) ∂μ) := by
  obtain ⟨h1, h2⟩ := BNS_cheb_core μ π _ _ hw1 hw2 hg1 hg2
  have hF : ∀ z : ℝ × ℝ, 0 ≤ (π z.1 - π z.2) * (Real.exp (t1 * π z.1) * Real.exp (t2 * π z.2) -
      Real.exp (t1 * π z.2) * Real.exp (t2 * π z.1)) := fun z =>
    BNS_pt π π t1 t2 ht (fun x y h => h) z.1 z.2
  have hnn : 0 ≤ ∫ z : ℝ × ℝ, (π z.1 - π z.2) * (Real.exp (t1 * π z.1) * Real.exp (t2 * π z.2) -
      Real.exp (t1 * π z.2) * Real.exp (t2 * π z.1)) ∂(μ.prod μ) := integral_nonneg hF
  by_contra hcon
  push_neg at hcon
  have hI : ∫ z : ℝ × ℝ, (π z.1 - π z.2) * (Real.exp (t1 * π z.1) * Real.exp (t2 * π z.2) -
      Real.exp (t1 * π z.2) * Real.exp (t2 * π z.1)) ∂(μ.prod μ) = 0 := by linarith
  have hae := (integral_eq_zero_iff_of_nonneg (μ := μ.prod μ) hF h2).1 hI
  have hae2 : ∀ᵐ z ∂(μ.prod μ), π z.1 = π z.2 := by
    filter_upwards [hae] with z hz
    by_contra hne
    have := BNS_pt_strict π t1 t2 ht z.1 z.2 hne
    simp only [Pi.zero_apply] at hz
    linarith
  have hae3 := Measure.ae_ae_of_ae_prod hae2
  have : μ ≠ 0 := by
    rintro rfl
    exact hnc ⟨0, by simp⟩
  haveI : NeZero μ := ⟨this⟩
  obtain ⟨x0, hx0⟩ := hae3.exists
  exact hnc ⟨π x0, by filter_upwards [hx0] with y hy using hy.symm⟩

theorem BNS_mean_eq (S : Set ℝ) (hS : MeasurableSet S) (π : ℝ → ℝ) (lam β : ℝ) :
    BoundedNV.Uniform.logitExp S (fun x => lam * π x) β π =
      (∫ v in S, π v * Real.exp ((lam / β) * π v)) / ∫ v in S, Real.exp ((lam / β) * π v) := by
  unfold BoundedNV.Uniform.logitExp BoundedNV.Uniform.logitDensity
  have e : ∀ y, π y * S.indicator (fun y => Real.exp ((fun x => lam * π x) y / β) /
      ∫ v in S, Real.exp ((fun x => lam * π x) v / β)) y =
      S.indicator (fun y => π y * Real.exp ((lam / β) * π y) /
        ∫ v in S, Real.exp ((lam / β) * π v)) y := by
    intro y
    by_cases hy : y ∈ S
    · simp only [Set.indicator_of_mem hy, BNS_e1]
      ring
    · simp [Set.indicator_of_notMem hy]
  simp_rw [e]
  rw [integral_indicator hS, integral_div]

theorem solution (S : Set ℝ) (hS : MeasurableSet S)
    (π : ℝ → ℝ) (hπ : Measurable π) (β lam₁ lam₂ : ℝ) (hβ : 0 < β) (hlam : lam₂ < lam₁)
    (hint₁ : IntegrableOn (fun x => Real.exp (lam₁ * π x / β)) S)
    (hint₂ : IntegrableOn (fun x => Real.exp (lam₂ * π x / β)) S)
    (hmom₁ : IntegrableOn (fun x => π x * Real.exp (lam₁ * π x / β)) S)
    (hmom₂ : IntegrableOn (fun x => π x * Real.exp (lam₂ * π x / β)) S)
    (hnc : ¬ ∃ k : ℝ, ∀ᵐ x ∂(volume.restrict S), π x = k) :
    BoundedNV.Uniform.logitExp S (fun x => lam₂ * π x) β π < BoundedNV.Uniform.logitExp S (fun x => lam₁ * π x) β π := by
  rw [BNS_mean_eq S hS, BNS_mean_eq S hS]
  simp only [BNS_e1] at hint₁ hint₂ hmom₁ hmom₂
  have hne : NeZero (volume.restrict S) := ⟨by
    intro h
    exact hnc ⟨0, by simp [h]⟩⟩
  have hZ1 := integral_exp_pos hint₁
  have hZ2 := integral_exp_pos hint₂
  have ht : lam₂ / β < lam₁ / β := div_lt_div_of_pos_right hlam hβ
  have key := BNS_strict (volume.restrict S) π (lam₁ / β) (lam₂ / β) ht hint₁ hint₂ hmom₁ hmom₂ hnc
  rw [div_lt_div_iff₀ hZ2 hZ1]
  exact key

