-- Prove2me | solution 1 for FirstPriceLearning.ContextLowerBound.lemma_13
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-24T06:16:51.62637+00:00
-- url     : https://prove2.me/submissions/cbc2d22f-1e53-42a7-a0d0-f296795d820d

import Mathlib

open Real
namespace CLBBH

/-- Binary Bretagnolle–Huber, interior case. -/
lemma binary_interior (x y : ℝ) (hx0 : 0 < x) (hx1 : x < 1) (hy0 : 0 < y) (hy1 : y < 1) :
    Real.exp (-(x * Real.log (x / y) + (1 - x) * Real.log ((1 - x) / (1 - y)))) ≤
      2 * (x + 1 - y) := by
  set p1 := Real.sqrt (y / x)
  set p2 := Real.sqrt ((1 - y) / (1 - x))
  have hp1 : 0 ≤ p1 := Real.sqrt_nonneg _
  have hp2 : 0 ≤ p2 := Real.sqrt_nonneg _
  have hp1pos : 0 < p1 := Real.sqrt_pos.mpr (by positivity)
  have hp2pos : 0 < p2 := Real.sqrt_pos.mpr (div_pos (by linarith) (by linarith))
  have hAMGM := Real.geom_mean_le_arith_mean2_weighted hx0.le (by linarith : 0 ≤ 1 - x) hp1 hp2
    (by ring)
  have hlog1 : Real.log p1 = (1 / 2) * Real.log (y / x) := by
    rw [Real.log_sqrt (by positivity)]; ring
  have hlog2 : Real.log p2 = (1 / 2) * Real.log ((1 - y) / (1 - x)) := by
    rw [Real.log_sqrt (div_pos (by linarith) (by linarith)).le]; ring
  have hgeo : p1 ^ x * p2 ^ (1 - x) =
      Real.exp (-(x * Real.log (x / y) + (1 - x) * Real.log ((1 - x) / (1 - y))) / 2) := by
    rw [Real.rpow_def_of_pos hp1pos, Real.rpow_def_of_pos hp2pos, ← Real.exp_add, hlog1, hlog2]
    congr 1
    have e1 : Real.log (x / y) = - Real.log (y / x) := by
      rw [← Real.log_inv, inv_div]
    have e2 : Real.log ((1 - x) / (1 - y)) = - Real.log ((1 - y) / (1 - x)) := by
      rw [← Real.log_inv, inv_div]
    rw [e1, e2]; ring
  set D := x * Real.log (x / y) + (1 - x) * Real.log ((1 - x) / (1 - y))
  set a := x * p1
  set b := (1 - x) * p2
  have ha2 : a ^ 2 = x * y := by
    simp only [a, p1]; rw [mul_pow, Real.sq_sqrt (by positivity)]; field_simp
  have hb2 : b ^ 2 = (1 - x) * (1 - y) := by
    simp only [b, p2]; rw [mul_pow, Real.sq_sqrt (div_pos (by linarith) (by linarith)).le]
    have : (1 - x) ≠ 0 := by linarith
    field_simp
  have ha : 0 ≤ a := by positivity
  have hb : 0 ≤ b := mul_nonneg (by linarith) hp2
  -- exp(-D) ≤ (a+b)^2
  have h1 : Real.exp (-D) ≤ (a + b) ^ 2 := by
    have hE : Real.exp (-D) = (Real.exp (-D / 2)) ^ 2 := by
      rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
    rw [hE]
    have : Real.exp (-D / 2) ≤ a + b := by rw [← hgeo]; exact hAMGM
    exact pow_le_pow_left₀ (Real.exp_pos _).le this 2
  -- (a+b)^2 ≤ 2(x+1-y)
  have hab : 2 * (a * b) ≤ x * (1 - x) + y * (1 - y) := by
    have hprod : (a * b) ^ 2 = (x * (1 - x)) * (y * (1 - y)) := by
      rw [mul_pow, ha2, hb2]; ring
    have hu : 0 ≤ x * (1 - x) := mul_nonneg hx0.le (by linarith)
    have hv : 0 ≤ y * (1 - y) := mul_nonneg hy0.le (by linarith)
    nlinarith [sq_nonneg (x * (1 - x) - y * (1 - y)), mul_nonneg ha hb,
      sq_nonneg (2 * (a * b) - (x * (1 - x) + y * (1 - y)))]
  nlinarith [ha2, hb2, hab]

/-- Binary Bretagnolle–Huber inequality in the `klFun` form, with the absolute-continuity side
conditions. -/
lemma binary (x y : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hy0 : 0 ≤ y) (hy1 : y ≤ 1)
    (h0 : y = 0 → x = 0) (h1 : y = 1 → x = 1) :
    Real.exp (-(y * InformationTheory.klFun (x / y) +
      (1 - y) * InformationTheory.klFun ((1 - x) / (1 - y)))) ≤ 2 * (x + 1 - y) := by
  rcases eq_or_lt_of_le hy0 with hy | hy
  · subst hy; rw [h0 rfl]; simp [InformationTheory.klFun_one]
  rcases eq_or_lt_of_le hy1 with hy' | hy'
  · subst hy'; rw [h1 rfl]; simp [InformationTheory.klFun_one]
  have hk1 : y * InformationTheory.klFun (x / y) = x * Real.log (x / y) + y - x := by
    rw [InformationTheory.klFun_apply]; field_simp
  have hk2 : (1 - y) * InformationTheory.klFun ((1 - x) / (1 - y)) =
      (1 - x) * Real.log ((1 - x) / (1 - y)) + (1 - y) - (1 - x) := by
    have : (1 - y) ≠ 0 := by linarith
    rw [InformationTheory.klFun_apply]; field_simp
  rw [hk1, hk2]
  have hD : x * Real.log (x / y) + y - x + ((1 - x) * Real.log ((1 - x) / (1 - y)) + (1 - y) - (1 - x))
      = x * Real.log (x / y) + (1 - x) * Real.log ((1 - x) / (1 - y)) := by ring
  rw [hD]
  rcases eq_or_lt_of_le hx0 with hx | hx
  · subst hx
    simp only [zero_mul, zero_add, sub_zero, one_mul]
    rw [Real.log_div (by norm_num) (by linarith), Real.log_one, zero_sub, neg_neg,
      Real.exp_log (by linarith)]
    linarith
  rcases eq_or_lt_of_le hx1 with hx' | hx'
  · subst hx'
    simp only [one_mul, sub_self, zero_mul, add_zero]
    rw [Real.log_div (by norm_num) (by linarith), Real.log_one, zero_sub, neg_neg,
      Real.exp_log (by linarith)]
    linarith
  exact binary_interior x y hx hx' hy hy'

end CLBBH

namespace CLBBH

open MeasureTheory InformationTheory

variable {Ω : Type} [MeasurableSpace Ω]

lemma set_jensen (P Q : Measure Ω) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (hac : P ≪ Q) (hint : Integrable (fun x => klFun (P.rnDeriv Q x).toReal) Q)
    {A : Set Ω} (hA : MeasurableSet A) :
    Q.real A * klFun (P.real A / Q.real A) ≤ ∫ x in A, klFun (P.rnDeriv Q x).toReal ∂Q := by
  by_cases hQA : Q A = 0
  · have : Q.real A = 0 := by simp [measureReal_def, hQA]
    rw [this, zero_mul]
    exact setIntegral_nonneg hA (fun x _ => klFun_nonneg ENNReal.toReal_nonneg)
  · have hJ := ConvexOn.map_set_average_le (μ := Q) (t := A)
      (f := fun x => (P.rnDeriv Q x).toReal) convexOn_klFun continuous_klFun.continuousOn
      isClosed_Ici hQA (measure_ne_top Q A)
      (Filter.Eventually.of_forall (fun x => (ENNReal.toReal_nonneg : (0:ℝ) ≤ _)))
      Measure.integrable_toReal_rnDeriv.integrableOn hint.integrableOn
    rw [setAverage_eq, setAverage_eq, Measure.setIntegral_toReal_rnDeriv hac A] at hJ
    have hpos : 0 < Q.real A := by
      rw [measureReal_def]; exact ENNReal.toReal_pos hQA (measure_ne_top Q A)
    simp only [smul_eq_mul, Function.comp_apply] at hJ
    rw [div_eq_inv_mul]
    have := mul_le_mul_of_nonneg_left hJ hpos.le
    rwa [← mul_assoc, mul_inv_cancel₀ hpos.ne', one_mul] at this

/-- Bretagnolle–Huber inequality for a measurable event. -/
lemma bretagnolle_huber (P Q : Measure Ω) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (hKL : klDiv P Q ≠ ⊤) {A : Set Ω} (hA : MeasurableSet A) :
    Real.exp (-(klDiv P Q).toReal) ≤ 2 * (P.real A + Q.real Aᶜ) := by
  obtain ⟨hac, h_int⟩ := klDiv_ne_top_iff.mp hKL
  have hint := (integrable_klFun_rnDeriv_iff hac).mpr h_int
  have hsplit : (klDiv P Q).toReal = (∫ x in A, klFun (P.rnDeriv Q x).toReal ∂Q) +
      ∫ x in Aᶜ, klFun (P.rnDeriv Q x).toReal ∂Q := by
    rw [toReal_klDiv_eq_integral_klFun hac, integral_add_compl hA hint]
  have j1 := set_jensen P Q hac hint hA
  have j2 := set_jensen P Q hac hint hA.compl
  rw [probReal_compl_eq_one_sub hA, probReal_compl_eq_one_sub hA] at j2
  set x := P.real A
  set y := Q.real A
  have hx0 : 0 ≤ x := measureReal_nonneg
  have hy0 : 0 ≤ y := measureReal_nonneg
  have hx1 : x ≤ 1 := by simp only [x]; exact measureReal_le_one
  have hy1 : y ≤ 1 := by simp only [y]; exact measureReal_le_one
  have h0 : y = 0 → x = 0 := by
    intro hy
    have : Q A = 0 := by
      have hy' : Q.real A = 0 := hy
      rw [measureReal_def, ENNReal.toReal_eq_zero_iff] at hy'
      exact hy'.resolve_right (measure_ne_top Q A)
    simp only [x, measureReal_def, hac this, ENNReal.toReal_zero]
  have h1 : y = 1 → x = 1 := by
    intro hy
    have hQc : Q.real Aᶜ = 0 := by rw [probReal_compl_eq_one_sub hA]; simp [y] at hy; linarith
    have : Q Aᶜ = 0 := by
      rw [measureReal_def, ENNReal.toReal_eq_zero_iff] at hQc
      exact hQc.resolve_right (measure_ne_top Q _)
    have hPc : P.real Aᶜ = 0 := by simp [measureReal_def, hac this]
    rw [probReal_compl_eq_one_sub hA] at hPc
    linarith
  have hb := binary x y hx0 hx1 hy0 hy1 h0 h1
  rw [probReal_compl_eq_one_sub hA]
  calc Real.exp (-(klDiv P Q).toReal)
      ≤ Real.exp (-(y * klFun (x / y) + (1 - y) * klFun ((1 - x) / (1 - y)))) := by
        apply Real.exp_le_exp.mpr; rw [hsplit]; linarith
    _ ≤ 2 * (x + 1 - y) := hb
    _ = 2 * (x + (1 - y)) := by ring

end CLBBH

open MeasureTheory InformationTheory

theorem solution {Ω : Type} [MeasurableSpace Ω] (n : ℕ) (Q : Fin (n + 1) → Measure Ω)
    (hQ : ∀ i, IsProbabilityMeasure (Q i)) (Ψ : Ω → Fin (n + 1)) (hΨ : Measurable Ψ) :
    1 / (2 * ((n : ℝ) + 1)) * ∑ i : Fin n,
        (if klDiv (Q 0) (Q i.succ) = ⊤ then 0
         else Real.exp (-(klDiv (Q 0) (Q i.succ)).toReal)) ≤
      1 / ((n : ℝ) + 1) * ∑ i : Fin (n + 1), (Q i {ω | Ψ ω ≠ i}).toReal := by
  have hA : ∀ j : Fin (n + 1), MeasurableSet {ω | Ψ ω = j} := fun j =>
    hΨ (measurableSet_singleton j)
  -- each term
  have hterm : ∀ i : Fin n,
      (if klDiv (Q 0) (Q i.succ) = ⊤ then 0
         else Real.exp (-(klDiv (Q 0) (Q i.succ)).toReal)) ≤
        2 * ((Q 0).real {ω | Ψ ω = i.succ} + (Q i.succ).real {ω | Ψ ω ≠ i.succ}) := by
    intro i
    split_ifs with h
    · positivity
    · have := CLBBH.bretagnolle_huber (Q 0) (Q i.succ) h (hA i.succ)
      have hc : {ω | Ψ ω = i.succ}ᶜ = {ω | Ψ ω ≠ i.succ} := by ext; simp
      rwa [hc] at this
  -- the events {Ψ = i+1} are disjoint and contained in {Ψ ≠ 0}
  have hsum0 : ∑ i : Fin n, (Q 0).real {ω | Ψ ω = i.succ} ≤ (Q 0).real {ω | Ψ ω ≠ 0} := by
    rw [← measureReal_biUnion_finset (s := Finset.univ)]
    · refine measureReal_mono ?_ (measure_ne_top _ _)
      intro ω hω
      simp only [Finset.mem_univ, Set.iUnion_true, Set.mem_iUnion, Set.mem_setOf_eq] at hω ⊢
      obtain ⟨i, hi⟩ := hω
      rw [hi]; exact Fin.succ_ne_zero i
    · intro i _ j _ hij
      simp only [Function.onFun]
      rw [Set.disjoint_left]
      intro ω h1 h2
      simp only [Set.mem_setOf_eq] at h1 h2
      exact hij (Fin.succ_injective _ (h1.symm.trans h2))
    · intro i _; exact hA i.succ
  have hmain : ∑ i : Fin n,
      (if klDiv (Q 0) (Q i.succ) = ⊤ then 0
         else Real.exp (-(klDiv (Q 0) (Q i.succ)).toReal)) ≤
      2 * ∑ i : Fin (n + 1), (Q i {ω | Ψ ω ≠ i}).toReal := by
    calc _ ≤ ∑ i : Fin n,
          2 * ((Q 0).real {ω | Ψ ω = i.succ} + (Q i.succ).real {ω | Ψ ω ≠ i.succ}) :=
          Finset.sum_le_sum (fun i _ => hterm i)
      _ = 2 * (∑ i : Fin n, (Q 0).real {ω | Ψ ω = i.succ} +
            ∑ i : Fin n, (Q i.succ).real {ω | Ψ ω ≠ i.succ}) := by
          rw [← Finset.sum_add_distrib, Finset.mul_sum]
      _ ≤ 2 * ((Q 0).real {ω | Ψ ω ≠ 0} +
            ∑ i : Fin n, (Q i.succ).real {ω | Ψ ω ≠ i.succ}) := by linarith
      _ = 2 * ∑ i : Fin (n + 1), (Q i {ω | Ψ ω ≠ i}).toReal := by
          rw [Fin.sum_univ_succ]; rfl
  have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  rw [show 1 / (2 * ((n : ℝ) + 1)) = (1 / ((n : ℝ) + 1)) / 2 by field_simp]
  rw [div_mul_eq_mul_div, div_le_iff₀ (by norm_num : (0:ℝ) < 2)]
  have := mul_le_mul_of_nonneg_left hmain (by positivity : (0:ℝ) ≤ 1 / ((n : ℝ) + 1))
  linarith
