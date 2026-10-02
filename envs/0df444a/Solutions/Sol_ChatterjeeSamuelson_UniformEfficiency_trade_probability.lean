-- Prove2me | solution 1 for ChatterjeeSamuelson.UniformEfficiency.trade_probability
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-01T17:12:17.840785+00:00
-- url     : https://prove2.me/submissions/433ab367-4e44-412b-b542-c29258be9653

import Mathlib
import Definitions.Def_ChatterjeeSamuelson_UniformEfficiency_IsExample1Pair
import Definitions.Def_ChatterjeeSamuelson_UniformEfficiency_tradeProb

set_option autoImplicit false

open Set

namespace P337bf25d

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
    · simp <;> ring
  · exact (by fun_prop : Continuous fun y : ℝ => c1 + c2 * (2 * y) + c3 * (3 * y ^ 2)).intervalIntegrable _ _

/-- on `[0, a]²` the trade event is the half-plane `m x ≤ y` -/
theorem trade_iff (k a : ℝ) (hk0 : 0 ≤ k) (hk1 : k ≤ 1) (hv : 0 < a) (S B : ℝ → ℝ)
    (hSB : ChatterjeeSamuelson.UniformEfficiency.IsExample1Pair k a S B)
    (x y : ℝ) (hx0 : 0 ≤ x) (hxa : x ≤ a) (hy0 : 0 ≤ y) (hya : y ≤ a) :
    S x ≤ B y ↔ (1 - k) / 2 * a + (1 + k) / (2 - k) * x ≤ y := by
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
  rw [hm]
  have sLx : ChatterjeeSamuelson.Shared.sellerLinear k a x = X + (1 - k) / 2 * a := rfl
  have bLy : ChatterjeeSamuelson.Shared.buyerLinear k a y = Y + D := rfl
  by_cases hxs : x ≤ (2 - k) / 2 * a
  · have hS := h1 x hx0 hxs
    rw [sLx] at hS
    by_cases hyb : (1 - k) / 2 * a ≤ y
    · have hB := h4 y hyb hya
      rw [bLy] at hB
      rw [hS, hB]
      constructor
      · intro h; nlinarith
      · intro h; nlinarith
    · have hB := h3 y hy0 (lt_of_not_ge hyb)
      rw [bLy] at hB
      constructor
      · intro h; exfalso; rw [hS] at h; apply hyb; nlinarith
      · intro h; exfalso; apply hyb; nlinarith
  · have hS := h2 x (lt_of_not_ge hxs) hxa
    rw [sLx] at hS
    have hBle : B y ≤ (2 - k) / 2 * a := by
      by_cases hyb : (1 - k) / 2 * a ≤ y
      · rw [h4 y hyb hya, bLy]; nlinarith
      · have := h3 y hy0 (lt_of_not_ge hyb)
        rw [bLy] at this; nlinarith
    constructor
    · intro h; exfalso; apply hxs; nlinarith
    · intro h; exfalso; apply hxs; nlinarith

theorem part1 (k vbar : ℝ) (hk0 : 0 ≤ k) (hk1 : k ≤ 1) (hv : 0 < vbar) (S B : ℝ → ℝ)
    (hSB : ChatterjeeSamuelson.UniformEfficiency.IsExample1Pair k vbar S B) :
    ChatterjeeSamuelson.UniformEfficiency.tradeProb vbar S B = (-k ^ 2 + k + 2) / 8 := by
  have hp : 0 < 1 + k := by linarith
  have hq : 0 < 2 - k := by linarith
  unfold ChatterjeeSamuelson.UniformEfficiency.tradeProb
  have hU : ChatterjeeSamuelson.Shared.unif vbar
      = (volume (Icc (0:ℝ) vbar))⁻¹ • volume.restrict (Icc (0:ℝ) vbar) := rfl
  have hbox : MeasurableSet (Icc (0:ℝ) vbar ×ˢ Icc (0:ℝ) vbar) :=
    measurableSet_Icc.prod measurableSet_Icc
  rw [hU, Measure.prod_smul_left, Measure.prod_smul_right, Measure.prod_restrict,
    Measure.smul_apply, Measure.smul_apply, Measure.restrict_apply' hbox, Real.volume_Icc]
  set c : ℝ := (1 - k) / 2 * vbar with hc
  set r : ℝ := (1 + k) / (2 - k) with hr
  have hr0 : 0 < r := by rw [hr]; positivity
  have hc0 : 0 ≤ c := by rw [hc]; nlinarith
  set T : Set (ℝ × ℝ) := (Icc (0:ℝ) vbar ×ˢ Icc (0:ℝ) vbar) ∩ {p | c + r * p.1 ≤ p.2} with hT
  have hTm : MeasurableSet T := hbox.inter (measurableSet_le (by fun_prop) measurable_snd)
  have hET : {p : ℝ × ℝ | S p.1 ≤ B p.2} ∩ (Icc (0:ℝ) vbar ×ˢ Icc (0:ℝ) vbar) = T := by
    ext p
    simp only [hT, Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_prod, Set.mem_Icc]
    constructor
    · rintro ⟨h, ⟨hx0, hxa⟩, ⟨hy0, hya⟩⟩
      exact ⟨⟨⟨hx0, hxa⟩, ⟨hy0, hya⟩⟩,
        (trade_iff k vbar hk0 hk1 hv S B hSB p.1 p.2 hx0 hxa hy0 hya).1 h⟩
    · rintro ⟨⟨⟨hx0, hxa⟩, ⟨hy0, hya⟩⟩, h⟩
      exact ⟨(trade_iff k vbar hk0 hk1 hv S B hSB p.1 p.2 hx0 hxa hy0 hya).2 h,
        ⟨hx0, hxa⟩, ⟨hy0, hya⟩⟩
  rw [hET]
  set g : ℝ → ℝ := fun y => (y - c) / r with hg
  have hslice : ∀ y : ℝ, volume ((fun x => (x, y)) ⁻¹' T)
      = (Icc c vbar).indicator (fun y => ENNReal.ofReal (g y)) y := by
    intro y
    by_cases hy : y ∈ Icc (0:ℝ) vbar
    · obtain ⟨hy0, hya⟩ := hy
      have hgle : g y ≤ vbar := by
        simp only [hg]
        rw [div_le_iff₀ hr0]
        have : (1 + k) / (2 - k) * (2 - k) = 1 + k := by field_simp
        have h2 : r * vbar = (1 + k) / (2 - k) * vbar := by rw [hr]
        rw [hc]
        have h3 : (1 + k) / (2 - k) ≥ (1 + k) / 2 := by
          apply div_le_div_of_nonneg_left hp.le hq (by linarith)
        nlinarith
      have hs : (fun x => (x, y)) ⁻¹' T = Icc 0 (g y) := by
        ext x
        simp only [hT, Set.mem_preimage, Set.mem_inter_iff, Set.mem_prod, Set.mem_Icc,
          Set.mem_setOf_eq]
        have key : c + r * x ≤ y ↔ x ≤ g y := by
          simp only [hg]; rw [le_div_iff₀ hr0]; constructor <;> intro h <;> linarith
        rw [key]
        constructor
        · rintro ⟨⟨⟨hx0, _⟩, _⟩, h⟩; exact ⟨hx0, h⟩
        · rintro ⟨hx0, h⟩; exact ⟨⟨⟨hx0, le_trans h hgle⟩, ⟨hy0, hya⟩⟩, h⟩
      rw [hs, Real.volume_Icc, sub_zero]
      by_cases hyc : y ∈ Icc c vbar
      · rw [Set.indicator_of_mem hyc]
      · rw [Set.indicator_of_notMem hyc]
        have : y < c := by
          by_contra hh; exact hyc ⟨le_of_not_gt hh, hya⟩
        apply ENNReal.ofReal_of_nonpos
        simp only [hg]
        exact div_nonpos_of_nonpos_of_nonneg (by linarith) hr0.le
    · have hs : (fun x => (x, y)) ⁻¹' T = ∅ := by
        ext x
        simp only [hT, Set.mem_preimage, Set.mem_inter_iff, Set.mem_prod, Set.mem_Icc,
          Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
        rintro ⟨⟨_, ⟨hy0, hya⟩⟩, _⟩
        exact hy ⟨hy0, hya⟩
      rw [hs, measure_empty, Set.indicator_of_notMem]
      rintro ⟨h1, h2⟩
      exact hy ⟨le_trans hc0 h1, h2⟩
  rw [Measure.prod_apply_symm hTm]
  simp_rw [hslice]
  rw [lintegral_indicator measurableSet_Icc]
  have hca : c ≤ vbar := by rw [hc]; nlinarith
  rw [← ofReal_integral_eq_lintegral_ofReal]
  rotate_left
  · exact (by fun_prop : Continuous g).continuousOn.integrableOn_compact isCompact_Icc
  · refine (ae_restrict_iff' measurableSet_Icc).2 (Filter.Eventually.of_forall ?_)
    intro y hy
    simp only [Pi.zero_apply, hg]
    exact div_nonneg (by linarith [hy.1]) hr0.le
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hca]
  have e2 : ∀ y, g y = -c / r + 1 / (2 * r) * (2 * y) + 0 * (3 * y ^ 2) := by
    intro y; simp only [hg]; field_simp; ring
  simp_rw [e2]
  rw [poly_int]
  have hI : 0 ≤ (-c / r * vbar + 1 / (2 * r) * vbar ^ 2 + 0 * vbar ^ 3) -
      (-c / r * c + 1 / (2 * r) * c ^ 2 + 0 * c ^ 3) := by
    have : (-c / r * vbar + 1 / (2 * r) * vbar ^ 2 + 0 * vbar ^ 3) -
      (-c / r * c + 1 / (2 * r) * c ^ 2 + 0 * c ^ 3) = (vbar - c) ^ 2 / (2 * r) := by
      field_simp; ring
    rw [this]; positivity
  rw [smul_eq_mul, smul_eq_mul, ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_inv,
    ENNReal.toReal_ofReal (by linarith), ENNReal.toReal_ofReal hI, sub_zero]
  simp only [hc, hr]
  field_simp
  ring

theorem part2 :
    IsMaxOn (fun κ : ℝ => (-κ ^ 2 + κ + 2) / 8) (Icc 0 1) (1 / 2) := by
  intro x _
  simp only [Set.mem_setOf_eq]
  nlinarith [sq_nonneg (x - 1 / 2)]

end P337bf25d

open Set ChatterjeeSamuelson.UniformEfficiency in
theorem solution (k vbar : ℝ) (hk0 : 0 ≤ k) (hk1 : k ≤ 1) (hv : 0 < vbar)
    (S B : ℝ → ℝ) (hSB : IsExample1Pair k vbar S B) :
    tradeProb vbar S B = (-k ^ 2 + k + 2) / 8 ∧
      IsMaxOn (fun κ : ℝ => (-κ ^ 2 + κ + 2) / 8) (Icc 0 1) (1 / 2) ∧
      (-(1 / 2 : ℝ) ^ 2 + 1 / 2 + 2) / 8 = 9 / 32 := by
  exact ⟨P337bf25d.part1 k vbar hk0 hk1 hv S B hSB, P337bf25d.part2, by norm_num⟩
