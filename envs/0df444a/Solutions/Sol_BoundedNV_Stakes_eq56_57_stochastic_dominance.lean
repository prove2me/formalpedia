-- Prove2me | solution 1 for BoundedNV.Stakes.eq56_57_stochastic_dominance
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T00:27:52.390014+00:00
-- url     : https://prove2.me/submissions/55204210-207d-4524-8d14-5e50f2e498d2

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


theorem BNS_set_eq (S : Set ℝ) (hS : MeasurableSet S) (π : ℝ → ℝ) (hπ : Measurable π) (k lam β : ℝ) :
    ∫ v in S ∩ {v | k ≤ π v}, BoundedNV.Uniform.logitDensity S (fun y => lam * π y) β v =
      (∫ v in S, (if k ≤ π v then (1:ℝ) else 0) * Real.exp ((lam / β) * π v)) /
        ∫ v in S, Real.exp ((lam / β) * π v) := by
  have hT : MeasurableSet {v | k ≤ π v} := measurableSet_le measurable_const hπ
  have h1 : ∫ v in S ∩ {v | k ≤ π v}, BoundedNV.Uniform.logitDensity S (fun y => lam * π y) β v =
      ∫ v in S ∩ {v | k ≤ π v}, Real.exp ((lam / β) * π v) /
        ∫ v in S, Real.exp ((lam / β) * π v) := by
    refine setIntegral_congr_fun (hS.inter hT) fun v hv => ?_
    have e1 : ∀ w, Real.exp (lam * π w / β) = Real.exp ((lam / β) * π w) := fun w => by
      congr 1; ring
    simp only [BoundedNV.Uniform.logitDensity, Set.indicator_of_mem hv.1, e1]
  rw [h1, integral_div]
  congr 1
  rw [← setIntegral_indicator hT]
  refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
  by_cases h : k ≤ π w <;> simp [Set.indicator, h]

theorem BNS_exp_eq (lam β : ℝ) (π : ℝ → ℝ) :
    (fun x => Real.exp (lam * π x / β)) = fun x => Real.exp ((lam / β) * π x) := by
  funext x; congr 1; ring

theorem solution (S : Set ℝ) (hS : MeasurableSet S) (hSpos : 0 < volume S)
    (π : ℝ → ℝ) (hπ : Measurable π) (β lam₁ lam₂ : ℝ) (hβ : 0 < β) (hlam : lam₂ < lam₁)
    (hint₁ : IntegrableOn (fun x => Real.exp (lam₁ * π x / β)) S)
    (hint₂ : IntegrableOn (fun x => Real.exp (lam₂ * π x / β)) S)
    (k : ℝ) :
    ∫ v in S ∩ {v | k ≤ π v}, BoundedNV.Uniform.logitDensity S (fun y => lam₂ * π y) β v ≤
      ∫ v in S ∩ {v | k ≤ π v}, BoundedNV.Uniform.logitDensity S (fun y => lam₁ * π y) β v := by
  rw [BNS_set_eq S hS π hπ, BNS_set_eq S hS π hπ]
  rw [BNS_exp_eq] at hint₁ hint₂
  set g : ℝ → ℝ := fun v => if k ≤ π v then (1:ℝ) else 0 with hg
  have hne : NeZero (volume.restrict S) := ⟨by
    intro h
    have := congrArg (fun m => m Set.univ) h
    simp [Measure.restrict_apply_univ] at this
    exact hSpos.ne' this⟩
  have hZ1 := integral_exp_pos hint₁
  have hZ2 := integral_exp_pos hint₂
  have hgm : Measurable g := Measurable.ite (measurableSet_le measurable_const hπ) measurable_const measurable_const
  have hgb : ∀ x, ‖g x‖ ≤ 1 := fun x => by by_cases h : k ≤ π x <;> simp [hg, h]
  have hg1 : Integrable (fun x => g x * Real.exp ((lam₁ / β) * π x)) (volume.restrict S) :=
    Integrable.bdd_mul (c := 1) hint₁ hgm.aestronglyMeasurable (Filter.Eventually.of_forall hgb)
  have hg2 : Integrable (fun x => g x * Real.exp ((lam₂ / β) * π x)) (volume.restrict S) :=
    Integrable.bdd_mul (c := 1) hint₂ hgm.aestronglyMeasurable (Filter.Eventually.of_forall hgb)
  have ht : lam₂ / β < lam₁ / β := div_lt_div_of_pos_right hlam hβ
  have key := BNS_cheb (volume.restrict S) π g (lam₁ / β) (lam₂ / β) ht hπ hgm
    (fun x y h => by
      by_cases h1 : k ≤ π x
      · have : k ≤ π y := h1.trans h
        simp [hg, h1, this]
      · by_cases h2 : k ≤ π y <;> simp [hg, h1, h2])
    hint₁ hint₂ hg1 hg2
  rw [div_le_div_iff₀ hZ2 hZ1]
  exact key

