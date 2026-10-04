-- Prove2me | solution 1 for ChatterjeeSamuelson.UniformEfficiency.total_profit
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-03T10:59:58.312526+00:00
-- url     : https://prove2.me/submissions/21c6c6a1-5cac-4c99-9090-f52776f24ca1

import Mathlib
import Definitions.Def_ChatterjeeSamuelson_UniformEfficiency_IsExample1Pair
import Definitions.Def_ChatterjeeSamuelson_UniformEfficiency_sellerExAnte
import Definitions.Def_ChatterjeeSamuelson_UniformEfficiency_buyerExAnte

set_option autoImplicit false

open Set

namespace P85975e4f

open MeasureTheory

/-- trade threshold for the buyer value -/
noncomputable def Lf (k a x : ℝ) : ℝ := (1 - k) / 2 * a + (1 + k) / (2 - k) * x

/-- seller profit on trade -/
noncomputable def hf (k a : ℝ) (p : ℝ × ℝ) : ℝ :=
  (k * p.2 + (1 - k) / 2 * a) / (1 + k) - p.1 / (2 - k)

/-- the trade region -/
def Kset (k a : ℝ) : Set (ℝ × ℝ) :=
  {p | 0 ≤ p.1} ∩ {p | p.1 ≤ (2 - k) / 2 * a} ∩ {p | Lf k a p.1 ≤ p.2} ∩ {p | p.2 ≤ a}

theorem measurableSet_Kset (k a : ℝ) : MeasurableSet (Kset k a) := by
  unfold Kset Lf
  refine ((( measurableSet_le measurable_const measurable_fst).inter
    (measurableSet_le measurable_fst measurable_const)).inter
    (measurableSet_le (by fun_prop) measurable_snd)).inter
    (measurableSet_le measurable_snd measurable_const)

theorem Kset_sub (k a : ℝ) (hk0 : 0 ≤ k) (hk1 : k ≤ 1) :
    Kset k a ⊆ Icc ((0 : ℝ), (0 : ℝ)) (a, a) := by
  rintro ⟨x, y⟩ ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩
  simp only [mem_ofPred_eq, Lf] at h1 h2 h3 h4
  have hq : 0 < 2 - k := by linarith
  have hmx : 0 ≤ (1 + k) / (2 - k) * x := mul_nonneg (div_nonneg (by linarith) hq.le) h1
  have ha : 0 ≤ a := by nlinarith
  refine ⟨⟨h1, ?_⟩, ⟨?_, h4⟩⟩
  · show 0 ≤ y; nlinarith
  · show x ≤ a; nlinarith

/-- pointwise identification of the seller's trade integrand on `[0, a]²` -/
theorem trade_eq (k a : ℝ) (hk0 : 0 ≤ k) (hk1 : k ≤ 1) (hv : 0 < a) (S B : ℝ → ℝ)
    (hSB : ChatterjeeSamuelson.UniformEfficiency.IsExample1Pair k a S B)
    (x y : ℝ) (hx0 : 0 ≤ x) (hxa : x ≤ a) (hy0 : 0 ≤ y) (hya : y ≤ a) :
    (if S x ≤ B y then k * B y + (1 - k) * S x - x else 0) =
      (Kset k a).indicator (hf k a) (x, y) := by
  obtain ⟨h1, h2, h3, h4⟩ := hSB
  have hp : 0 < 1 + k := by linarith
  have hq : 0 < 2 - k := by linarith
  set X := x / (2 - k) with hXdef
  set Y := y / (1 + k) with hYdef
  have hX : X * (2 - k) = x := div_mul_cancel₀ x hq.ne'
  have hY : Y * (1 + k) = y := div_mul_cancel₀ y hp.ne'
  have hX0 : 0 ≤ X := div_nonneg hx0 hq.le
  set D := k * (1 - k) / (2 * (1 + k)) * a with hDdef
  have hD : D * (2 * (1 + k)) = k * (1 - k) * a := by
    rw [hDdef]; field_simp
  have hm : (1 + k) / (2 - k) * x = (1 + k) * X := by rw [hXdef]; ring
  have sLx : ChatterjeeSamuelson.Shared.sellerLinear k a x = X + (1 - k) / 2 * a := rfl
  have bLy : ChatterjeeSamuelson.Shared.buyerLinear k a y = Y + D := rfl
  have hK : (x, y) ∈ Kset k a ↔ (1 - k) / 2 * a + (1 + k) * X ≤ y := by
    simp only [Kset, Lf, mem_inter_iff, mem_ofPred_eq, hm]
    constructor
    · rintro ⟨⟨⟨_, _⟩, h⟩, _⟩; exact h
    · intro h
      refine ⟨⟨⟨hx0, ?_⟩, h⟩, hya⟩
      have : (1 + k) * X ≤ (1 + k) / 2 * a := by linarith
      have hX' : X ≤ a / 2 := by nlinarith
      nlinarith
  have hval : k * (Y + D) + (1 - k) * (X + (1 - k) / 2 * a) - x = hf k a (x, y) := by
    simp only [hf]
    rw [hXdef, hYdef, hDdef]
    field_simp
    ring
  by_cases hxs : x ≤ (2 - k) / 2 * a
  · have hS := h1 x hx0 hxs
    rw [sLx] at hS
    by_cases hyb : (1 - k) / 2 * a ≤ y
    · have hB := h4 y hyb hya
      rw [bLy] at hB
      rw [hS, hB]
      by_cases ht : (1 - k) / 2 * a + (1 + k) * X ≤ y
      · have : X + (1 - k) / 2 * a ≤ Y + D := by nlinarith
        rw [if_pos this, indicator_of_mem (hK.2 ht), hval]
      · have : ¬ (X + (1 - k) / 2 * a ≤ Y + D) := by
          intro h; apply ht; nlinarith
        rw [if_neg this, indicator_of_notMem (fun h => ht (hK.1 h))]
    · have hB := h3 y hy0 (lt_of_not_ge hyb)
      rw [bLy] at hB
      have : ¬ (S x ≤ B y) := by
        rw [hS]; intro h; apply hyb; nlinarith
      have ht : ¬ ((1 - k) / 2 * a + (1 + k) * X ≤ y) := by
        intro h; apply hyb; nlinarith
      rw [if_neg this, indicator_of_notMem (fun h => ht (hK.1 h))]
  · have hS := h2 x (lt_of_not_ge hxs) hxa
    rw [sLx] at hS
    have hBle : B y ≤ (2 - k) / 2 * a := by
      by_cases hyb : (1 - k) / 2 * a ≤ y
      · rw [h4 y hyb hya, bLy]; nlinarith
      · have := h3 y hy0 (lt_of_not_ge hyb)
        rw [bLy] at this; nlinarith
    have : ¬ (S x ≤ B y) := by
      intro h; apply hxs; nlinarith
    have ht : ¬ ((1 - k) / 2 * a + (1 + k) * X ≤ y) := by
      intro h; apply hxs; nlinarith
    rw [if_neg this, indicator_of_notMem (fun h => ht (hK.1 h))]

theorem integral_unif (a : ℝ) (hv : 0 < a) (f : ℝ → ℝ) :
    ∫ y, f y ∂(ChatterjeeSamuelson.Shared.unif a) = a⁻¹ * ∫ y in Icc 0 a, f y := by
  unfold ChatterjeeSamuelson.Shared.unif ProbabilityTheory.cond
  rw [integral_smul_measure, Real.volume_Icc, sub_zero, ENNReal.toReal_inv,
    ENNReal.toReal_ofReal hv.le, smul_eq_mul]

/-- inner integral -/
theorem inner_eq (k a : ℝ) (hk0 : 0 ≤ k) (hk1 : k ≤ 1) (hv : 0 < a) (x : ℝ) :
    ∫ y in Icc 0 a, (Kset k a).indicator (hf k a) (x, y) =
      (Icc 0 ((2 - k) / 2 * a)).indicator
        (fun x => (1 + k) / (2 * (2 - k)) * ((2 - k) / 2 * a - x) ^ 2) x := by
  have hp : 0 < 1 + k := by linarith
  have hq : 0 < 2 - k := by linarith
  by_cases hx : x ∈ Icc 0 ((2 - k) / 2 * a)
  · rw [indicator_of_mem hx]
    have hfun : (fun y => (Kset k a).indicator (hf k a) (x, y)) =
        (Icc (Lf k a x) a).indicator (fun y => hf k a (x, y)) := by
      funext y
      by_cases hy : y ∈ Icc (Lf k a x) a
      · rw [indicator_of_mem hy, indicator_of_mem]
        exact ⟨⟨⟨hx.1, hx.2⟩, hy.1⟩, hy.2⟩
      · rw [indicator_of_notMem hy, indicator_of_notMem]
        rintro ⟨⟨⟨_, _⟩, h3⟩, h4⟩
        exact hy ⟨h3, h4⟩
    have hL0 : 0 ≤ Lf k a x := by
      unfold Lf
      have := mul_nonneg (div_nonneg hp.le hq.le) hx.1
      have : 0 ≤ (1 - k) / 2 * a := by
        apply mul_nonneg _ hv.le; linarith
      linarith
    have hLa : Lf k a x ≤ a := by
      unfold Lf
      have h2 := hx.2
      have : (1 + k) / (2 - k) * x ≤ (1 + k) / (2 - k) * ((2 - k) / 2 * a) :=
        mul_le_mul_of_nonneg_left h2 (div_nonneg hp.le hq.le)
      have e : (1 + k) / (2 - k) * ((2 - k) / 2 * a) = (1 + k) / 2 * a := by
        field_simp
      linarith
    change ∫ y in Icc 0 a, (fun y => (Kset k a).indicator (hf k a) (x, y)) y = _
    rw [hfun, setIntegral_indicator measurableSet_Icc, Icc_inter_Icc, max_eq_right hL0,
      min_self, integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hLa]
    have hderiv : ∀ y ∈ uIcc (Lf k a x) a, HasDerivAt
        (fun y => (k * (y ^ 2 / 2) + (1 - k) / 2 * a * y) / (1 + k) - x * y / (2 - k))
        (hf k a (x, y)) y := by
      intro y _
      have h2 : HasDerivAt (fun y : ℝ => y ^ 2) (2 * y) y := by
        simpa using hasDerivAt_pow 2 y
      have h := ((((h2.div_const 2).const_mul k).add
        ((hasDerivAt_id' y).const_mul ((1 - k) / 2 * a))).div_const (1 + k)).sub
        (((hasDerivAt_id' y).const_mul x).div_const (2 - k))
      refine h.congr_deriv ?_
      simp only [hf]
      ring
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv]
    · simp only [Lf]
      field_simp
      ring
    · apply Continuous.intervalIntegrable
      unfold hf; fun_prop
  · rw [indicator_of_notMem hx]
    have : ∀ y, (Kset k a).indicator (hf k a) (x, y) = 0 := by
      intro y
      apply indicator_of_notMem
      rintro ⟨⟨⟨h1, h2⟩, _⟩, _⟩
      exact hx ⟨h1, h2⟩
    simp [this]

theorem outer_eq (k a : ℝ) (hk0 : 0 ≤ k) (hk1 : k ≤ 1) (hv : 0 < a) :
    ∫ x in Icc 0 a, (Icc 0 ((2 - k) / 2 * a)).indicator
        (fun x => (1 + k) / (2 * (2 - k)) * ((2 - k) / 2 * a - x) ^ 2) x =
      a ^ 3 / 48 * (2 - k) ^ 2 * (1 + k) := by
  have hp : 0 < 1 + k := by linarith
  have hq : 0 < 2 - k := by linarith
  have hx0 : 0 ≤ (2 - k) / 2 * a := by positivity
  have hx0a : (2 - k) / 2 * a ≤ a := by nlinarith
  rw [setIntegral_indicator measurableSet_Icc, Icc_inter_Icc, max_self, min_eq_right hx0a,
    integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hx0]
  have hderiv : ∀ x ∈ uIcc 0 ((2 - k) / 2 * a), HasDerivAt
      (fun x => -((1 + k) / (2 * (2 - k)) * (((2 - k) / 2 * a - x) ^ 3 / 3)))
      ((1 + k) / (2 * (2 - k)) * ((2 - k) / 2 * a - x) ^ 2) x := by
    intro x _
    have h1 : HasDerivAt (fun x => (2 - k) / 2 * a - x) (-1) x := by
      simpa using (hasDerivAt_id x).const_sub ((2 - k) / 2 * a)
    have h3 : HasDerivAt (fun x => ((2 - k) / 2 * a - x) ^ 3)
        (3 * ((2 - k) / 2 * a - x) ^ 2 * (-1)) x := by
      have hc := (hasDerivAt_pow 3 ((2 - k) / 2 * a - x)).comp x h1
      simpa [Function.comp_def] using hc
    have h := ((h3.div_const 3).const_mul ((1 + k) / (2 * (2 - k)))).neg
    refine h.congr_deriv ?_
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv]
  · field_simp
    ring
  · apply Continuous.intervalIntegrable
    fun_prop

end P85975e4f

open P85975e4f in
open MeasureTheory in
theorem probe_main (k vbar : ℝ) (hk0 : 0 ≤ k) (hk1 : k ≤ 1) (hv : 0 < vbar)
    (S B : ℝ → ℝ) (hSB : ChatterjeeSamuelson.UniformEfficiency.IsExample1Pair k vbar S B) :
    ChatterjeeSamuelson.UniformEfficiency.sellerExAnte k vbar S B =
      vbar / 48 * (2 - k) ^ 2 * (1 + k) := by
  unfold ChatterjeeSamuelson.UniformEfficiency.sellerExAnte
  set μ := ChatterjeeSamuelson.Shared.unif vbar with hμ
  have : IsProbabilityMeasure μ := by
    rw [hμ]
    exact ProbabilityTheory.cond_isProbabilityMeasure_of_finite
      (by simp [Real.volume_Icc, hv]) (by simp [Real.volume_Icc])
  have hbox : ∀ᵐ x ∂μ, x ∈ Icc 0 vbar := ProbabilityTheory.ae_cond_mem measurableSet_Icc
  have hae : ∀ᵐ p ∂(μ.prod μ), p ∈ (Icc 0 vbar) ×ˢ (Icc 0 vbar) := by
    rw [Measure.ae_prod_mem_iff_ae_ae_mem (measurableSet_Icc.prod measurableSet_Icc)]
    filter_upwards [hbox] with x hx
    filter_upwards [hbox] with y hy
    exact ⟨hx, hy⟩
  have hcongr : (fun p : ℝ × ℝ => if S p.1 ≤ B p.2 then k * B p.2 + (1 - k) * S p.1 - p.1
      else 0) =ᵐ[μ.prod μ] (Kset k vbar).indicator (hf k vbar) := by
    filter_upwards [hae] with p hp
    obtain ⟨⟨hx0, hxa⟩, ⟨hy0, hya⟩⟩ := hp
    exact trade_eq k vbar hk0 hk1 hv S B hSB p.1 p.2 hx0 hxa hy0 hya
  rw [integral_congr_ae hcongr]
  have hint : Integrable ((Kset k vbar).indicator (hf k vbar)) (μ.prod μ) := by
    rw [integrable_indicator_iff (measurableSet_Kset k vbar)]
    refine IntegrableOn.mono_set ?_ (Kset_sub k vbar hk0 hk1)
    apply ContinuousOn.integrableOn_compact isCompact_Icc
    apply Continuous.continuousOn
    unfold hf; fun_prop
  rw [integral_prod _ hint]
  simp_rw [hμ, integral_unif vbar hv]
  simp_rw [inner_eq k vbar hk0 hk1 hv]
  rw [integral_const_mul, outer_eq k vbar hk0 hk1 hv]
  field_simp

namespace A1792fec

open MeasureTheory

theorem poly_int (lo hi c1 c2 c3 : ℝ) :
    ∫ y in lo..hi, (c1 + c2 * (2 * y) + c3 * (3 * y ^ 2)) =
      (c1 * hi + c2 * hi ^ 2 + c3 * hi ^ 3) - (c1 * lo + c2 * lo ^ 2 + c3 * lo ^ 3) := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro x _
    have h := (((hasDerivAt_id x).const_mul c1).add ((hasDerivAt_pow 2 x).const_mul c2)).add
      ((hasDerivAt_pow 3 x).const_mul c3)
    convert h using 1
    · funext y; simp
    · simp; try ring
  · exact (by fun_prop : Continuous fun y : ℝ => c1 + c2 * (2 * y) + c3 * (3 * y ^ 2)).intervalIntegrable _ _

/-- pointwise identification of the trade integrand on `[0, a]²` -/
theorem trade_eq (k a : ℝ) (hk0 : 0 ≤ k) (hk1 : k ≤ 1) (hv : 0 < a) (S B : ℝ → ℝ)
    (hSB : ChatterjeeSamuelson.UniformEfficiency.IsExample1Pair k a S B)
    (x y : ℝ) (hx0 : 0 ≤ x) (hxa : x ≤ a) (hy0 : 0 ≤ y) (hya : y ≤ a) :
    (if S x ≤ B y then y - (k * B y + (1 - k) * S x) else 0) =
      (if (1 - k) / 2 * a + (1 + k) / (2 - k) * x ≤ y then
        (y - (1 - k) / 2 * a) / (1 + k) - (1 - k) / (2 - k) * x else 0) := by
  obtain ⟨h1, h2, h3, h4⟩ := hSB
  have hp : 0 < 1 + k := by linarith
  have hq : 0 < 2 - k := by linarith
  set X := x / (2 - k) with hXdef
  set Y := y / (1 + k) with hYdef
  have hX : X * (2 - k) = x := div_mul_cancel₀ x hq.ne'
  have hY : Y * (1 + k) = y := div_mul_cancel₀ y hp.ne'
  have hX0 : 0 ≤ X := div_nonneg hx0 hq.le
  set D := k * (1 - k) / (2 * (1 + k)) * a with hDdef
  have hD : D * (2 * (1 + k)) = k * (1 - k) * a := by
    rw [hDdef]; field_simp
  have hm : (1 + k) / (2 - k) * x = (1 + k) * X := by rw [hXdef]; ring
  have hc : (1 - k) / (2 - k) * x = (1 - k) * X := by rw [hXdef]; ring
  have hdiv : (y - (1 - k) / 2 * a) / (1 + k) = Y - (1 - k) / (2 * (1 + k)) * a := by
    rw [hYdef]; field_simp
  have hE : (1 - k) / (2 * (1 + k)) * a * (2 * (1 + k)) = (1 - k) * a := by field_simp
  set E := (1 - k) / (2 * (1 + k)) * a with hEdef
  rw [hm, hc, hdiv]
  have sLx : ChatterjeeSamuelson.Shared.sellerLinear k a x = X + (1 - k) / 2 * a := rfl
  have bLy : ChatterjeeSamuelson.Shared.buyerLinear k a y = Y + D := rfl
  by_cases hxs : x ≤ (2 - k) / 2 * a
  · have hS := h1 x hx0 hxs
    rw [sLx] at hS
    by_cases hyb : (1 - k) / 2 * a ≤ y
    · have hB := h4 y hyb hya
      rw [bLy] at hB
      rw [hS, hB]
      by_cases ht : (1 - k) / 2 * a + (1 + k) * X ≤ y
      · have : X + (1 - k) / 2 * a ≤ Y + D := by nlinarith
        rw [if_pos this, if_pos ht]
        nlinarith
      · have : ¬ (X + (1 - k) / 2 * a ≤ Y + D) := by
          intro h; apply ht; nlinarith
        rw [if_neg this, if_neg ht]
    · have hB := h3 y hy0 (lt_of_not_ge hyb)
      rw [bLy] at hB
      have : ¬ (S x ≤ B y) := by
        rw [hS]; intro h; apply hyb; nlinarith
      have ht : ¬ ((1 - k) / 2 * a + (1 + k) * X ≤ y) := by
        intro h; apply hyb; nlinarith
      rw [if_neg this, if_neg ht]
  · have hS := h2 x (lt_of_not_ge hxs) hxa
    rw [sLx] at hS
    have hYD : Y + D ≤ (2 - k) / 2 * a := by
      have e : (Y + D) * (2 * (1 + k)) = 2 * y + k * (1 - k) * a := by
        linear_combination 2 * hY + hD
      have e2 : ((2 - k) / 2 * a) * (2 * (1 + k)) = 2 * a + k * (1 - k) * a := by ring
      exact le_of_mul_le_mul_right (by rw [e, e2]; linarith) (by positivity)
    have hBle : B y ≤ (2 - k) / 2 * a := by
      by_cases hyb : (1 - k) / 2 * a ≤ y
      · rw [h4 y hyb hya, bLy]; exact hYD
      · have := h3 y hy0 (lt_of_not_ge hyb)
        rw [bLy] at this; linarith
    have hXgt : a / 2 < X := by
      have : (a / 2) * (2 - k) < X * (2 - k) := by
        rw [hX]; have := lt_of_not_ge hxs; linarith
      exact lt_of_mul_lt_mul_right this hq.le
    have : ¬ (S x ≤ B y) := by
      intro h; linarith
    have ht : ¬ ((1 - k) / 2 * a + (1 + k) * X ≤ y) := by
      intro h
      have : (1 + k) * (a / 2) < (1 + k) * X := mul_lt_mul_of_pos_left hXgt hp
      linarith
    rw [if_neg this, if_neg ht]

theorem part1 (k vbar : ℝ) (hk0 : 0 ≤ k) (hk1 : k ≤ 1) (hv : 0 < vbar) (S B : ℝ → ℝ)
    (hSB : ChatterjeeSamuelson.UniformEfficiency.IsExample1Pair k vbar S B) :
    ChatterjeeSamuelson.UniformEfficiency.buyerExAnte k vbar S B
      = vbar / 48 * (1 + k) ^ 2 * (2 - k) := by
  have hp : 0 < 1 + k := by linarith
  have hq : 0 < 2 - k := by linarith
  unfold ChatterjeeSamuelson.UniformEfficiency.buyerExAnte
  have hU : ChatterjeeSamuelson.Shared.unif vbar
      = (volume (Icc (0:ℝ) vbar))⁻¹ • volume.restrict (Icc (0:ℝ) vbar) := rfl
  rw [hU, Measure.prod_smul_left, Measure.prod_smul_right, Measure.prod_restrict,
    integral_smul_measure, integral_smul_measure, Real.volume_Icc]
  have hvt : (ENNReal.ofReal (vbar - 0))⁻¹.toReal = vbar⁻¹ := by
    rw [ENNReal.toReal_inv, ENNReal.toReal_ofReal (by linarith), sub_zero]
  rw [hvt]
  set m : ℝ → ℝ := fun x => (1 - k) / 2 * vbar + (1 + k) / (2 - k) * x with hmdef
  set h : ℝ × ℝ → ℝ := fun p => (p.2 - (1 - k) / 2 * vbar) / (1 + k) - (1 - k) / (2 - k) * p.1
    with hhdef
  have hcongr : ∀ p ∈ Icc (0:ℝ) vbar ×ˢ Icc (0:ℝ) vbar,
      (if S p.1 ≤ B p.2 then p.2 - (k * B p.2 + (1 - k) * S p.1) else 0)
        = (Set.indicator {q : ℝ × ℝ | m q.1 ≤ q.2} h) p := by
    intro p hp'
    obtain ⟨⟨hx0, hxa⟩, ⟨hy0, hya⟩⟩ := hp'
    rw [trade_eq k vbar hk0 hk1 hv S B hSB p.1 p.2 hx0 hxa hy0 hya, Set.indicator_apply]
    rfl
  rw [setIntegral_congr_fun (measurableSet_Icc.prod measurableSet_Icc) hcongr]
  have hint : IntegrableOn (Set.indicator {q : ℝ × ℝ | m q.1 ≤ q.2} h)
      (Icc (0:ℝ) vbar ×ˢ Icc (0:ℝ) vbar) (volume.prod volume) := by
    apply IntegrableOn.indicator _ (measurableSet_le (by fun_prop) (by fun_prop))
    exact (by fun_prop : Continuous h).continuousOn.integrableOn_compact
      (isCompact_Icc.prod isCompact_Icc)
  rw [setIntegral_prod _ hint]
  set s1 : ℝ := (2 - k) / 2 * vbar with hs1
  set c1 : ℝ → ℝ := fun x => -((1 - k) / 2 * vbar) / (1 + k) - (1 - k) / (2 - k) * x with hc1
  set c2 : ℝ := 1 / (2 * (1 + k)) with hc2
  set P : ℝ → ℝ := fun x => (c1 x * vbar + c2 * vbar ^ 2 + 0 * vbar ^ 3)
      - (c1 x * m x + c2 * m x ^ 2 + 0 * m x ^ 3) with hPdef
  have hinner : ∀ x ∈ Icc (0:ℝ) vbar,
      (∫ y in Icc (0:ℝ) vbar, Set.indicator {q : ℝ × ℝ | m q.1 ≤ q.2} h (x, y))
        = Set.indicator (Iic s1) P x := by
    intro x hx
    obtain ⟨hx0, hxa⟩ := hx
    have e1 : (fun y => Set.indicator {q : ℝ × ℝ | m q.1 ≤ q.2} h (x, y))
        = Set.indicator (Ici (m x)) (fun y => h (x, y)) := by
      funext y
      simp only [Set.indicator_apply, Set.mem_ofPred_eq, Set.mem_Ici]
    rw [e1, setIntegral_indicator measurableSet_Ici]
    by_cases hxs : x ≤ s1
    · have hm0 : 0 ≤ m x := by
        simp only [hmdef]; have : 0 ≤ (1 + k) / (2 - k) * x := by positivity
        nlinarith
      have hma : m x ≤ vbar := by
        simp only [hmdef]
        have : (1 + k) / (2 - k) * x ≤ (1 + k) / (2 - k) * s1 :=
          mul_le_mul_of_nonneg_left hxs (by positivity)
        have h2 : (1 + k) / (2 - k) * s1 = (1 + k) / 2 * vbar := by
          rw [hs1]; field_simp
        nlinarith
      have hset : Icc (0:ℝ) vbar ∩ Ici (m x) = Icc (m x) vbar := by
        ext y; simp only [Set.mem_inter_iff, Set.mem_Icc, Set.mem_Ici]
        constructor
        · rintro ⟨⟨_, h2⟩, h3⟩; exact ⟨h3, h2⟩
        · rintro ⟨h1, h2⟩; exact ⟨⟨le_trans hm0 h1, h2⟩, h1⟩
      rw [hset, integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hma,
        Set.indicator_of_mem (Set.mem_Iic.2 hxs)]
      have e2 : ∀ y, h (x, y) = c1 x + c2 * (2 * y) + 0 * (3 * y ^ 2) := by
        intro y; simp only [hhdef, hc1, hc2]; field_simp; ring
      simp_rw [e2]
      rw [poly_int]
    · have hma : vbar < m x := by
        simp only [hmdef]
        have : (1 + k) / (2 - k) * s1 < (1 + k) / (2 - k) * x :=
          mul_lt_mul_of_pos_left (lt_of_not_ge hxs) (by positivity)
        have h2 : (1 + k) / (2 - k) * s1 = (1 + k) / 2 * vbar := by
          rw [hs1]; field_simp
        nlinarith
      have hset : Icc (0:ℝ) vbar ∩ Ici (m x) = ∅ := by
        ext y; simp only [Set.mem_inter_iff, Set.mem_Icc, Set.mem_Ici, Set.mem_empty_iff_false,
          iff_false]
        rintro ⟨⟨_, h2⟩, h3⟩; linarith
      rw [hset, Measure.restrict_empty, integral_zero_measure,
        Set.indicator_of_notMem (by simpa using hxs)]
  rw [setIntegral_congr_fun measurableSet_Icc hinner, setIntegral_indicator measurableSet_Iic]
  have hs1a : s1 ≤ vbar := by rw [hs1]; nlinarith
  have hs10 : 0 ≤ s1 := by rw [hs1]; positivity
  have hset : Icc (0:ℝ) vbar ∩ Iic s1 = Icc 0 s1 := by
    ext y; simp only [Set.mem_inter_iff, Set.mem_Icc, Set.mem_Iic]
    constructor
    · rintro ⟨⟨h1, _⟩, h3⟩; exact ⟨h1, h3⟩
    · rintro ⟨h1, h2⟩; exact ⟨⟨h1, le_trans h2 hs1a⟩, h2⟩
  rw [hset, integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hs10]
  set d1 : ℝ := (1 + k) * vbar ^ 2 / 8 with hd1
  set d2 : ℝ := -((1 - k ^ 2) * vbar / (4 * (2 - k))) with hd2
  set d3 : ℝ := (1 + k) * (1 - 2 * k) / (6 * (2 - k) ^ 2) with hd3
  have e3 : ∀ x, P x = d1 + d2 * (2 * x) + d3 * (3 * x ^ 2) := by
    intro x; simp only [hPdef, hc1, hc2, hmdef, hd1, hd2, hd3]; field_simp; ring
  simp_rw [e3]
  rw [poly_int]
  simp only [hd1, hd2, hd3, hs1, smul_eq_mul]
  field_simp
  ring

theorem part2 (vbar : ℝ) (hv : 0 < vbar) :
    StrictMonoOn (fun κ : ℝ => vbar / 48 * (1 + κ) ^ 2 * (2 - κ)) (Icc 0 1) := by
  intro x hx y hy hxy
  obtain ⟨hx0, hx1⟩ := hx
  obtain ⟨hy0, hy1⟩ := hy
  have key : (1 + x) ^ 2 * (2 - x) < (1 + y) ^ 2 * (2 - y) := by
    have e : (1 + y) ^ 2 * (2 - y) - (1 + x) ^ 2 * (2 - x)
        = (y - x) * (3 - (x ^ 2 + x * y + y ^ 2)) := by ring
    have h3 : 0 < 3 - (x ^ 2 + x * y + y ^ 2) := by nlinarith
    have := mul_pos (sub_pos.2 hxy) h3
    linarith
  have hc : 0 < vbar / 48 := by positivity
  have := mul_lt_mul_of_pos_left key hc
  simp only
  calc vbar / 48 * (1 + x) ^ 2 * (2 - x) = vbar / 48 * ((1 + x) ^ 2 * (2 - x)) := by ring
    _ < vbar / 48 * ((1 + y) ^ 2 * (2 - y)) := this
    _ = vbar / 48 * (1 + y) ^ 2 * (2 - y) := by ring

end A1792fec

open Set ChatterjeeSamuelson.UniformEfficiency in
theorem solution (k vbar : ℝ) (hk0 : 0 ≤ k) (hk1 : k ≤ 1) (hv : 0 < vbar)
    (S B : ℝ → ℝ) (hSB : IsExample1Pair k vbar S B) :
    sellerExAnte k vbar S B + buyerExAnte k vbar S B = vbar / 16 * (1 + k) * (2 - k) ∧
      IsMaxOn (fun κ : ℝ => vbar / 16 * (1 + κ) * (2 - κ)) (Icc 0 1) (1 / 2) ∧
      vbar / 16 * (1 + 1 / 2) * (2 - 1 / 2) = 9 / 64 * vbar := by
  refine ⟨?_, ?_, by ring⟩
  · rw [probe_main k vbar hk0 hk1 hv S B hSB, A1792fec.part1 k vbar hk0 hk1 hv S B hSB]
    ring
  · intro x _
    show vbar / 16 * (1 + x) * (2 - x) ≤ vbar / 16 * (1 + 1 / 2) * (2 - 1 / 2)
    have h : (1 + x) * (2 - x) ≤ (1 + 1 / 2) * (2 - 1 / 2) := by nlinarith [sq_nonneg (x - 1 / 2)]
    have hc : 0 ≤ vbar / 16 := by positivity
    have := mul_le_mul_of_nonneg_left h hc
    calc vbar / 16 * (1 + x) * (2 - x) = vbar / 16 * ((1 + x) * (2 - x)) := by ring
      _ ≤ vbar / 16 * ((1 + 1 / 2) * (2 - 1 / 2)) := this
      _ = vbar / 16 * (1 + 1 / 2) * (2 - 1 / 2) := by ring
