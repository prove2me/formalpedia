-- Prove2me | solution 1 for CountingLLL.RandomRAM.product_estimator_accuracy
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T05:17:51.940491+00:00
-- url     : https://prove2.me/submissions/f431f908-fb2d-4db6-ab6c-640463855ae2

import Theorems.Thm_CountingLLL_RandomRAM_product_relative_second_moment

set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

private theorem exp_variance_margin (ε : ℝ) (h0 : 0 ≤ ε) (h1 : ε ≤ 1) :
    Real.exp (ε ^ 2 / 20) - 1 ≤ ε ^ 2 / 16 := by
  have h2 : 0 ≤ ε ^ 2 := sq_nonneg ε
  have h3 : ε ^ 2 ≤ 1 := by nlinarith
  have ht0 : 0 ≤ ε ^ 2 / 20 := by positivity
  have ht1 : ε ^ 2 / 20 ≤ 1 / 20 := by nlinarith
  have ha : |ε ^ 2 / 20| ≤ 1 := by rw [abs_of_nonneg ht0]; linarith
  have hh := Real.abs_exp_sub_one_sub_id_le ha
  have hbound : Real.exp (ε ^ 2 / 20) - 1 - ε ^ 2 / 20 ≤ (ε ^ 2 / 20) ^ 2 :=
    (le_abs_self _).trans hh
  nlinarith [sq_nonneg (ε ^ 2 / 20)]

/-- Independent square-integrable factors have a square-integrable product. -/
private theorem independent_product_memLp {Ω ι : Type} [MeasurableSpace Ω] [Fintype ι]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : ι → Ω → ℝ)
    (hind : iIndepFun X μ) (hL2 : ∀ i, MemLp (X i) 2 μ) :
    MemLp (fun ω => ∏ i, X i ω) 2 μ := by
  classical
  let μi : ι → Measure ℝ := fun i => μ.map (X i)
  have hm : ∀ i, AEMeasurable (X i) μ := fun i => (hL2 i).aemeasurable
  letI (i : ι) : IsProbabilityMeasure (μi i) := Measure.isProbabilityMeasure_map (hm i)
  have hfact : ∀ i, Integrable (fun x : ℝ => x ^ 2) (μi i) := by
    intro i
    apply (integrable_map_measure (by fun_prop) (hm i)).2
    simpa [Function.comp_def, Real.norm_eq_abs, sq_abs] using (hL2 i).integrable_norm_pow (p := 2) (by norm_num)
  have hprod : Integrable (fun x : ι → ℝ => ∏ i, (x i) ^ 2) (Measure.pi μi) :=
    Integrable.fintype_prod hfact
  have hvec : AEMeasurable (fun ω i => X i ω) μ := aemeasurable_pi_iff.mpr hm
  have hmap : Measure.map (fun ω i => X i ω) μ = Measure.pi μi := hind.map_fun_eq_pi_map hm
  rw [← hmap] at hprod
  have hcomp := hprod.comp_aemeasurable hvec
  have hpow : Integrable (fun ω => ‖∏ i, X i ω‖ ^ (2 : ℕ)) μ := by
    simpa only [Function.comp_def, Real.norm_eq_abs, sq_abs, Finset.prod_pow] using hcomp
  have hstrong : AEStronglyMeasurable (fun ω => ∏ i, X i ω) μ :=
    Finset.aestronglyMeasurable_fun_prod Finset.univ (fun i _ => (hL2 i).aestronglyMeasurable)
  apply (integrable_norm_rpow_iff hstrong (by norm_num) (by simp)).1
  simpa using hpow

/-- Source equation (34), from a mean and relative-variance estimate. -/
theorem chebyshev_accuracy {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (Y : Ω → ℝ) (Z ε : ℝ)
    (hY : MemLp Y 2 μ) (hZ : 0 < Z) (he0 : 0 < ε) (he1 : ε ≤ 1)
    (hmean : (∫ ω, Y ω ∂μ) = Z)
    (hvar : variance Y μ ≤ (Real.exp (ε ^ 2 / 20) - 1) * Z ^ 2) :
    (15 / 16 : ℝ≥0∞) ≤ μ {ω | (1 - ε) * Z ≤ Y ω ∧ Y ω ≤ (1 + ε) * Z} := by
  let G : Set Ω := {ω | (1 - ε) * Z ≤ Y ω ∧ Y ω ≤ (1 + ε) * Z}
  let B : Set Ω := {ω | ε * Z ≤ |Y ω - Z|}
  have hthresh : 0 < ε * Z := mul_pos he0 hZ
  have hv : variance Y μ ≤ ε ^ 2 / 16 * Z ^ 2 :=
    hvar.trans (mul_le_mul_of_nonneg_right (exp_variance_margin ε he0.le he1) (sq_nonneg Z))
  have hd : 0 < (ε * Z) ^ 2 := sq_pos_of_pos hthresh
  have hquot : variance Y μ / (ε * Z) ^ 2 ≤ 1 / 16 := by
    apply (div_le_iff₀ hd).2
    nlinarith [hv]
  have hbad : μ B ≤ ENNReal.ofReal (1 / 16 : ℝ) := by
    have hc := meas_ge_le_variance_div_sq hY hthresh
    rw [hmean] at hc
    exact hc.trans (ENNReal.ofReal_le_ofReal hquot)
  have hbad' : μ.real B ≤ (1 / 16 : ℝ) := by
    have hh := ENNReal.toReal_mono ENNReal.ofReal_ne_top hbad
    simpa [Measure.real, ENNReal.toReal_ofReal] using hh
  have hcover : Set.univ ⊆ G ∪ B := by
    intro ω _
    by_cases hb : ω ∈ B
    · exact Or.inr hb
    · left
      have hs : |Y ω - Z| < ε * Z := lt_of_not_ge hb
      have hs' := abs_lt.mp hs
      constructor <;> nlinarith
  have hsum : (1 : ℝ) ≤ μ.real G + μ.real B := by
    calc
      1 = μ.real Set.univ := probReal_univ.symm
      _ ≤ μ.real (G ∪ B) := measureReal_mono hcover
      _ ≤ μ.real G + μ.real B := measureReal_union_le G B
  have hgood : (15 / 16 : ℝ) ≤ μ.real G := by linarith
  have h15 : (15 / 16 : ℝ≥0∞) ≠ ⊤ := ENNReal.div_ne_top (by simp) (by norm_num)
  have h := (ENNReal.toReal_le_toReal h15 (measure_ne_top μ G)).mp
    (by simpa [Measure.real, ENNReal.toReal_div] using hgood)
  exact h

/-- Accuracy of a product estimator under the exact variance budget from #442 §5.3. -/
theorem product_estimator_accuracy {Ω ι : Type} [MeasurableSpace Ω] [Fintype ι]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : ι → Ω → ℝ) (ε : ℝ)
    (hind : iIndepFun X μ) (hL2 : ∀ i, MemLp (X i) 2 μ)
    (hmean : ∀ i, (∫ ω, X i ω ∂μ) ≠ 0)
    (hZ : 0 < ∏ i, ∫ ω, X i ω ∂μ)
    (he0 : 0 < ε) (he1 : ε ≤ 1)
    (hbudget : (∑ i, variance (X i) μ / (∫ ω, X i ω ∂μ) ^ 2) ≤ ε ^ 2 / 20) :
    (15 / 16 : ℝ≥0∞) ≤ μ {ω |
      (1 - ε) * (∏ i, ∫ ω, X i ω ∂μ) ≤ (∏ i, X i ω) ∧
      (∏ i, X i ω) ≤ (1 + ε) * (∏ i, ∫ ω, X i ω ∂μ)} := by
  have hprodL2 : MemLp (fun ω => ∏ i, X i ω) 2 μ :=
    independent_product_memLp μ X hind hL2
  let Z : ℝ := ∏ i, ∫ ω, X i ω ∂μ
  let Y : Ω → ℝ := fun ω => ∏ i, X i ω
  have hYmean : (∫ ω, Y ω ∂μ) = Z := by
    exact hind.integral_fun_prod_eq_prod_integral (fun i => (hL2 i).aestronglyMeasurable)
  have hratio := (CountingLLL.RandomRAM.product_relative_second_moment μ X hind hL2 hmean).2
  have hratio' : (∫ ω, Y ω ^ 2 ∂μ) / Z ^ 2 ≤ Real.exp (ε ^ 2 / 20) :=
    hratio.trans (Real.exp_le_exp.mpr hbudget)
  have hnum : (∫ ω, Y ω ^ 2 ∂μ) ≤ Real.exp (ε ^ 2 / 20) * Z ^ 2 :=
    (div_le_iff₀ (sq_pos_of_pos hZ)).mp hratio'
  have hvar : variance Y μ ≤ (Real.exp (ε ^ 2 / 20) - 1) * Z ^ 2 := by
    rw [variance_eq_sub hprodL2]
    simp only [Pi.pow_apply, hYmean]
    nlinarith
  exact chebyshev_accuracy μ Y Z ε hprodL2 hZ he0 he1 hYmean hvar

/-- Scaled product form of the accuracy estimate in equation (34). -/
theorem solution {Ω ι : Type} [MeasurableSpace Ω] [Fintype ι]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : ι → Ω → ℝ) (a ε : ℝ)
    (ha : 0 < a) (hind : iIndepFun X μ) (hL2 : ∀ i, MemLp (X i) 2 μ)
    (hmean : ∀ i, (∫ ω, X i ω ∂μ) ≠ 0)
    (hZ : 0 < ∏ i, ∫ ω, X i ω ∂μ)
    (he0 : 0 < ε) (he1 : ε ≤ 1)
    (hbudget : (∑ i, variance (X i) μ / (∫ ω, X i ω ∂μ) ^ 2) ≤ ε ^ 2 / 20) :
    (15 / 16 : ℝ≥0∞) ≤ μ {ω |
      (1 - ε) * (a * (∏ i, ∫ ω, X i ω ∂μ)) ≤ a * (∏ i, X i ω) ∧
      a * (∏ i, X i ω) ≤ (1 + ε) * (a * (∏ i, ∫ ω, X i ω ∂μ))} := by
  apply (product_estimator_accuracy μ X ε hind hL2 hmean hZ he0 he1 hbudget).trans
  apply measure_mono
  intro ω hω
  constructor <;> nlinarith [mul_le_mul_of_nonneg_left hω.1 ha.le,
    mul_le_mul_of_nonneg_left hω.2 ha.le]
