-- Prove2me | solution 1 for BilateralProfitRegular.eq_47
-- status  : ACCEPTED   (prove)
-- author  : @sim2000dg
-- created : 2026-11-18T15:09:56.490783+00:00
-- url     : https://prove2.me/submissions/e763fd58-4159-4d3c-ae34-91b9ee8cbb21

import Mathlib
import Theorems.Thm_BilateralProfitMHR_positive_density_profit_facts
import Definitions.Def_BilateralProfitRegular_Stochastic
import Definitions.Def_BilateralProfitRegular_Auxiliary


section BundlePart000




namespace BilateralProfitRegular

open Set MechanismDesign.BilateralTrade BilateralProfit MeasureTheory

private theorem intT_subset_unitSq : intT ⊆ BilateralProfitMHR.unitSq := by
  intro x hx
  exact ⟨⟨hx.1.le, (hx.2.1.trans hx.2.2).le⟩,
    ⟨(hx.1.trans hx.2.1).le, hx.2.2.le⟩⟩

private theorem onUnit_facts (E : Environment) (hE : OnUnit E) :
    (∀ a, 0 ≤ P E a ∧ P E a ≤ 1) ∧
    (∀ a ∈ BilateralProfitMHR.unitSq, P E a = E.cdfS a.1 * (1 - E.cdfB a.2)) ∧
    (∀ a ∈ BilateralProfitMHR.unitSq, 0 < mu E a ↔ a ∈ intT) ∧
    (0 < muStar E ∧ muStar E ≤ 1) ∧
    (∀ a ∈ BilateralProfitMHR.unitSq, mu E a ≤ muStar E) ∧
    (∃ a ∈ intT, mu E a = muStar E) := by
  obtain ⟨_, _, hp, hf, _, _, _, _, hm, hs, hu, he, _⟩ :=
    BilateralProfitMHR.positive_density_profit_facts E hE
  exact ⟨hp, hf, hm, hs, hu, he⟩

private theorem P_factor (E : Environment) (hE : OnUnit E) {x : ℝ × ℝ}
    (hx : x ∈ BilateralProfitMHR.unitSq) :
    P E x = E.cdfS x.1 * (1 - E.cdfB x.2) :=
  (onUnit_facts E hE).2.1 x hx

private theorem mu_formula (E : Environment) (x : ℝ × ℝ) :
    mu E x = (x.2 - x.1) * P E x := rfl

private theorem mu_le_muStar (E : Environment) (hE : OnUnit E) {x : ℝ × ℝ}
    (hx : x ∈ BilateralProfitMHR.unitSq) : mu E x ≤ muStar E :=
  (onUnit_facts E hE).2.2.2.2.1 x hx

private theorem cdfS_pos (E : Environment) (hE : OnUnit E) {p : ℝ} (hp : p ∈ Ioc 0 1) :
    0 < E.cdfS p := by
  have hf := E.fS_intervalIntegrable
  rw [hE.1, hE.2.1] at hf
  unfold Environment.cdfS
  rw [hE.1]
  apply intervalIntegral.intervalIntegral_pos_of_pos_on _ _ hp.1
  · apply hf.mono_set
    rw [uIcc_of_le hp.1.le, uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    exact Icc_subset_Icc le_rfl hp.2
  · intro t ht
    exact E.fS_pos t (by rw [hE.1, hE.2.1]; exact ⟨ht.1.le, ht.2.le.trans hp.2⟩)

private theorem tailB_eq_integral (E : Environment) (hE : OnUnit E) {q : ℝ} (hq : q ∈ Icc 0 1) :
    1 - E.cdfB q = ∫ t in q..1, E.fB t := by
  have hf := E.fB_intervalIntegrable
  have ht := E.fB_integral
  rw [hE.2.2.1, hE.2.2.2] at hf ht
  have h₁ := hf.mono_set (show uIcc 0 q ⊆ uIcc 0 1 by
    rw [uIcc_of_le hq.1, uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    exact Icc_subset_Icc le_rfl hq.2)
  have h₂ := hf.mono_set (show uIcc q 1 ⊆ uIcc 0 1 by
    rw [uIcc_of_le hq.2, uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    exact Icc_subset_Icc hq.1 le_rfl)
  rw [Environment.cdfB, hE.2.2.1]
  linarith [intervalIntegral.integral_add_adjacent_intervals h₁ h₂]

private theorem tailB_pos (E : Environment) (hE : OnUnit E) {q : ℝ} (hq : q ∈ Ico 0 1) :
    0 < 1 - E.cdfB q := by
  rw [tailB_eq_integral E hE ⟨hq.1, hq.2.le⟩]
  have hf := E.fB_intervalIntegrable
  rw [hE.2.2.1, hE.2.2.2] at hf
  apply intervalIntegral.intervalIntegral_pos_of_pos_on _ _ hq.2
  · apply hf.mono_set
    rw [uIcc_of_le hq.2.le, uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    exact Icc_subset_Icc hq.1 le_rfl
  · intro t ht
    exact E.fB_pos t (by rw [hE.2.2.1, hE.2.2.2]; exact ⟨hq.1.trans ht.1.le, ht.2.le⟩)

private theorem intT_cdf_pos (E : Environment) (hE : OnUnit E) {x : ℝ × ℝ} (hx : x ∈ intT) :
    0 < E.cdfS x.1 ∧ 0 < 1 - E.cdfB x.2 :=
  ⟨cdfS_pos E hE ⟨hx.1, (intT_subset_unitSq hx).1.2⟩,
    tailB_pos E hE ⟨(intT_subset_unitSq hx).2.1, hx.2.2⟩⟩

private theorem balance_pos (E : Environment) (hE : OnUnit E) {x : ℝ × ℝ} (hx : x ∈ intT) :
    0 < balance E x :=
  Real.sqrt_pos.2 (div_pos (intT_cdf_pos E hE hx).1 (intT_cdf_pos E hE hx).2)

private theorem balance_sq (E : Environment) (hE : OnUnit E) {x : ℝ × ℝ} (hx : x ∈ intT) :
    balance E x ^ 2 = E.cdfS x.1 / (1 - E.cdfB x.2) :=
  Real.sq_sqrt (div_pos (intT_cdf_pos E hE hx).1 (intT_cdf_pos E hE hx).2).le

private theorem auxProfit_pos (E : Environment) (hE : OnUnit E) {lam : ℝ} (hlam : 0 < lam)
    {x : ℝ × ℝ} (hx : x ∈ intT) : 0 < auxProfit E lam x := by
  have hm := intT_cdf_pos E hE hx
  unfold auxProfit
  exact div_pos (mul_pos (by norm_num) (sub_pos.mpr hx.2.1))
    (pow_pos (add_pos (div_pos hlam hm.1) (div_pos (inv_pos.mpr hlam) hm.2)) _)

private theorem eq_42 (E : Environment) (hE : RegularUnit E) (x z : ℝ × ℝ) (hx : x ∈ intT)
    (hz : z ∈ intT) (ρ : ℝ) (hρ : 0 < ρ) :
    1 / auxProfit E (ρ * balance E z) x =
      P E z / (4 * (x.2 - x.1)) * (ρ / P E (x.1, z.2) + ρ⁻¹ / P E (z.1, x.2)) ^ 2 := by
  have hX := intT_subset_unitSq hx
  have hZ := intT_subset_unitSq hz
  rw [P_factor E hE.1 hZ, P_factor E hE.1 (x := (x.1,z.2)) ⟨hX.1,hZ.2⟩,
    P_factor E hE.1 (x := (z.1,x.2)) ⟨hZ.1,hX.2⟩]
  have hsX := (intT_cdf_pos E hE.1 hx).1.ne'
  have hbX := (intT_cdf_pos E hE.1 hx).2.ne'
  have hsZ := (intT_cdf_pos E hE.1 hz).1.ne'
  have hbZ := (intT_cdf_pos E hE.1 hz).2.ne'
  have hlZ := (balance_pos E hE.1 hz).ne'
  have hs := balance_sq E hE.1 hz
  have hei : (balance E z)⁻¹ = balance E z * (1 - E.cdfB z.2) / E.cdfS z.1 := by
    apply inv_eq_of_mul_eq_one_left
    calc
      balance E z * (1 - E.cdfB z.2) / E.cdfS z.1 * balance E z =
          (balance E z ^ 2 * (1 - E.cdfB z.2)) / E.cdfS z.1 := by ring
      _ = 1 := by rw [hs, div_mul_cancel₀ _ hbZ, div_self hsZ]
  have he :
      ρ * balance E z / E.cdfS x.1 + (ρ * balance E z)⁻¹ / (1 - E.cdfB x.2) =
      (balance E z * (1 - E.cdfB z.2)) *
        (ρ / (E.cdfS x.1 * (1 - E.cdfB z.2)) + ρ⁻¹ / (E.cdfS z.1 * (1 - E.cdfB x.2))) := by
    rw [mul_inv, hei]
    field_simp
  have hsq : (balance E z * (1 - E.cdfB z.2)) ^ 2 =
      E.cdfS z.1 * (1 - E.cdfB z.2) := by
    rw [mul_pow, hs, pow_two, ← mul_assoc, div_mul_cancel₀ _ hbZ]
  simp only [auxProfit, one_div, inv_div]
  rw [he, mul_pow, hsq]
  ring

private theorem eq_47 (E : Environment) (hE : RegularUnit E) (x z : ℝ × ℝ) (hx : x ∈ intT)
    (hz : z ∈ intT) :
    Real.log (balance E x / balance E z) =
      1 / 2 * Real.log (P E (x.1, z.2) / P E (z.1, x.2)) := by
  have hX := intT_subset_unitSq hx
  have hZ := intT_subset_unitSq hz
  have hbX := (intT_cdf_pos E hE.1 hx).2.ne'
  have hsZ := (intT_cdf_pos E hE.1 hz).1.ne'
  have hbZ := (intT_cdf_pos E hE.1 hz).2.ne'
  have he : (balance E x / balance E z)^2 = P E (x.1, z.2) / P E (z.1, x.2) := by
    rw [div_pow, balance_sq E hE.1 hx, balance_sq E hE.1 hz,
      P_factor E hE.1 (x := (x.1,z.2)) ⟨hX.1,hZ.2⟩,
      P_factor E hE.1 (x := (z.1,x.2)) ⟨hZ.1,hX.2⟩]
    dsimp
    field_simp
  rw [← he, Real.log_pow]
  ring

end BilateralProfitRegular
end BundlePart000

open BilateralProfitRegular
open MechanismDesign.BilateralTrade

theorem solution (E : Environment) (hE : RegularUnit E) (x z : ℝ × ℝ) (hx : x ∈ intT)
    (hz : z ∈ intT) :
    Real.log (balance E x / balance E z) =
      1 / 2 * Real.log (P E (x.1, z.2) / P E (z.1, x.2)) := by
  exact BilateralProfitRegular.eq_47 E hE x z hx hz
