-- Prove2me | solution 1 for ChatterjeeSamuelson.UniformEfficiency.buyer_ex_ante_profit
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-01T16:48:08.819975+00:00
-- url     : https://prove2.me/submissions/af75ba8d-b17c-4d3b-aa9f-f2dd0ad2dea4

import Mathlib
import Definitions.Def_ChatterjeeSamuelson_UniformEfficiency_IsExample1Pair
import Definitions.Def_ChatterjeeSamuelson_UniformEfficiency_buyerExAnte

set_option autoImplicit false

open Set

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
    buyerExAnte k vbar S B = vbar / 48 * (1 + k) ^ 2 * (2 - k) ∧
      StrictMonoOn (fun κ : ℝ => vbar / 48 * (1 + κ) ^ 2 * (2 - κ)) (Icc 0 1) := by
  exact ⟨A1792fec.part1 k vbar hk0 hk1 hv S B hSB, A1792fec.part2 vbar hv⟩
