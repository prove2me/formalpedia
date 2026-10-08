-- Prove2me | solution 1 for CachonPushPull.Pareto.optimal_quantity_prices
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-05T20:13:05.770403+00:00
-- url     : https://prove2.me/submissions/0384b53a-0bec-40b6-88c7-a1386d408d90

import Mathlib
import Definitions.Def_CachonPushPull_Pareto_Profits

set_option autoImplicit false

namespace CachonPushPull04889b81

open MeasureTheory ProbabilityTheory CachonPushPull.Pareto

lemma cdf_lt_one_of_nonneg (μ : Measure ℝ) [IsProbabilityMeasure μ] (f : ℝ → ℝ)
    (hD : DemandModel μ f) {q : ℝ} (hq : 0 ≤ q) : cdf μ q < 1 := by
  have h1 : cdf μ q < cdf μ (q + 1) :=
    hD.strictMonoOn (Set.mem_Ici.mpr hq) (Set.mem_Ici.mpr (by linarith)) (by linarith)
  exact lt_of_lt_of_le h1 (cdf_le_one μ _)

/-- Key strict inequality: `F(q) y - ∫₀^y F < F(q) q - ∫₀^q F` for `y ≠ q`, `y, q ≥ 0`. -/
lemma key (μ : Measure ℝ) [IsProbabilityMeasure μ] (f : ℝ → ℝ)
    (hD : DemandModel μ f) {q y : ℝ} (hq : 0 ≤ q) (hy : 0 ≤ y) (hne : y ≠ q) :
    cdf μ q * y - ∫ x in (0 : ℝ)..y, cdf μ x < cdf μ q * q - ∫ x in (0 : ℝ)..q, cdf μ x := by
  have hint : ∀ a b : ℝ, IntervalIntegrable (cdf μ) volume a b :=
    fun a b => (monotone_cdf μ).intervalIntegrable
  have hsplit : (∫ x in (0 : ℝ)..y, cdf μ x) - ∫ x in (0 : ℝ)..q, cdf μ x
      = ∫ x in q..y, cdf μ x := by
    rw [intervalIntegral.integral_interval_sub_left (hint 0 y) (hint 0 q)]
  set m := (q + y) / 2 with hm
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · -- y < q
    have hym : y ≤ m := by rw [hm]; linarith
    have hmq : m ≤ q := by rw [hm]; linarith
    have hFm : cdf μ m < cdf μ q :=
      hD.strictMonoOn (Set.mem_Ici.mpr (by rw [hm]; linarith)) (Set.mem_Ici.mpr hq)
        (by rw [hm]; linarith)
    have h1 : ∫ x in y..m, cdf μ x ≤ ∫ x in y..m, cdf μ m :=
      intervalIntegral.integral_mono_on hym (hint y m) intervalIntegrable_const
        (fun x hx => monotone_cdf μ hx.2)
    have h2 : ∫ x in m..q, cdf μ x ≤ ∫ x in m..q, cdf μ q :=
      intervalIntegral.integral_mono_on hmq (hint m q) intervalIntegrable_const
        (fun x hx => monotone_cdf μ hx.2)
    have hadd : (∫ x in y..m, cdf μ x) + ∫ x in m..q, cdf μ x = ∫ x in y..q, cdf μ x :=
      intervalIntegral.integral_add_adjacent_intervals (hint y m) (hint m q)
    have hswap : ∫ x in q..y, cdf μ x = -∫ x in y..q, cdf μ x :=
      intervalIntegral.integral_symm y q
    simp only [intervalIntegral.integral_const, smul_eq_mul] at h1 h2
    have hpos : 0 < m - y := by rw [hm]; linarith
    have : (m - y) * cdf μ m < (m - y) * cdf μ q := mul_lt_mul_of_pos_left hFm hpos
    nlinarith
  · -- q < y
    have hqm : q ≤ m := by rw [hm]; linarith
    have hmy : m ≤ y := by rw [hm]; linarith
    have hFm : cdf μ q < cdf μ m :=
      hD.strictMonoOn (Set.mem_Ici.mpr hq) (Set.mem_Ici.mpr (by rw [hm]; linarith))
        (by rw [hm]; linarith)
    have h1 : ∫ x in q..m, cdf μ q ≤ ∫ x in q..m, cdf μ x :=
      intervalIntegral.integral_mono_on hqm intervalIntegrable_const (hint q m)
        (fun x hx => monotone_cdf μ hx.1)
    have h2 : ∫ x in m..y, cdf μ m ≤ ∫ x in m..y, cdf μ x :=
      intervalIntegral.integral_mono_on hmy intervalIntegrable_const (hint m y)
        (fun x hx => monotone_cdf μ hx.1)
    have hadd : (∫ x in q..m, cdf μ x) + ∫ x in m..y, cdf μ x = ∫ x in q..y, cdf μ x :=
      intervalIntegral.integral_add_adjacent_intervals (hint q m) (hint m y)
    simp only [intervalIntegral.integral_const, smul_eq_mul] at h1 h2
    have hpos : 0 < y - m := by rw [hm]; linarith
    have : (y - m) * cdf μ q < (y - m) * cdf μ m := mul_lt_mul_of_pos_left hFm hpos
    nlinarith

end CachonPushPull04889b81

open MeasureTheory ProbabilityTheory CachonPushPull.Pareto in
theorem solution (μ : Measure ℝ) [IsProbabilityMeasure μ] (f : ℝ → ℝ)
    (hD : DemandModel μ f) (p c v : ℝ) (hvc : v < c) (hcp : c < p) :
    StrictAntiOn (pushPrice μ p v) (Set.Ici 0) ∧
    StrictMonoOn (pullPrice μ c v) (Set.Ici 0) ∧
    ∀ q : ℝ, 0 ≤ q →
      (∀ y : ℝ, 0 ≤ y → y ≠ q →
        pushRetailerProfitAt μ p v (pushPrice μ p v q) y <
          pushRetailerProfitAt μ p v (pushPrice μ p v q) q) ∧
      (∀ y : ℝ, 0 ≤ y → y ≠ q →
        pullSupplierProfitAt μ c v (pullPrice μ c v q) y <
          pullSupplierProfitAt μ c v (pullPrice μ c v q) q) := by
  have hpv : 0 < p - v := by linarith
  have hcv : 0 < c - v := by linarith
  refine ⟨?_, ?_, ?_⟩
  · intro a ha b hb hab
    have := hD.strictMonoOn ha hb hab
    simp only [pushPrice]
    nlinarith
  · intro a ha b hb hab
    have hF := hD.strictMonoOn ha hb hab
    have ha1 := CachonPushPull04889b81.cdf_lt_one_of_nonneg μ f hD (Set.mem_Ici.mp ha)
    have hb1 := CachonPushPull04889b81.cdf_lt_one_of_nonneg μ f hD (Set.mem_Ici.mp hb)
    simp only [pullPrice]
    rw [div_lt_div_iff₀ (by linarith) (by linarith)]
    nlinarith
  · intro q hq
    have hk := fun y (hy : 0 ≤ y) (hne : y ≠ q) =>
      CachonPushPull04889b81.key μ f hD hq hy hne
    have hq1 := CachonPushPull04889b81.cdf_lt_one_of_nonneg μ f hD hq
    refine ⟨?_, ?_⟩
    · intro y hy hne
      have := hk y hy hne
      simp only [pushRetailerProfitAt, pushPrice, S]
      nlinarith
    · intro y hy hne
      have := hk y hy hne
      have h1 : 0 < 1 - cdf μ q := by linarith
      have hw : pullPrice μ c v q - v = (c - v) / (1 - cdf μ q) := by
        simp only [pullPrice]
        field_simp
        ring
      simp only [pullSupplierProfitAt, S]
      rw [hw]
      have hd : 0 < (c - v) / (1 - cdf μ q) := div_pos hcv h1
      have e : ∀ t : ℝ, (c - v) / (1 - cdf μ q) * (t - ∫ x in (0 : ℝ)..t, cdf μ x) - (c - v) * t
          = (c - v) / (1 - cdf μ q) * (cdf μ q * t - ∫ x in (0 : ℝ)..t, cdf μ x) := by
        intro t
        field_simp
        ring
      rw [e y, e q]
      exact mul_lt_mul_of_pos_left this hd
