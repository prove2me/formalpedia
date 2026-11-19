-- Prove2me | solution 1 for BilateralProfitRegular.lemma_6_2
-- status  : ACCEPTED   (prove)
-- author  : @sim2000dg
-- created : 2026-11-18T15:21:42.050535+00:00
-- url     : https://prove2.me/submissions/1b9c071b-0f2e-4cc8-a337-3819a2795743

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


section BundlePart001


namespace BilateralProfitRegular

open MechanismDesign.BilateralTrade

private theorem hasDerivAt_tanh (t : ℝ) : HasDerivAt Real.tanh (1 / Real.cosh t ^ 2) t := by
  have hd := (Real.hasDerivAt_sinh t).div (Real.hasDerivAt_cosh t) (Real.cosh_pos t).ne'
  have he : Real.tanh = Real.sinh / Real.cosh := funext Real.tanh_eq_sinh_div_cosh
  rw [he]
  simpa only [← pow_two, Real.cosh_sq_sub_sinh_sq] using hd

private theorem tanh_lipschitz : LipschitzWith 1 Real.tanh := by
  apply lipschitzWith_of_nnnorm_deriv_le (fun t => (hasDerivAt_tanh t).differentiableAt)
  intro t
  rw [(hasDerivAt_tanh t).deriv]
  change ‖(1 / Real.cosh t ^ 2 : ℝ)‖ ≤ 1
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  apply (div_le_iff₀ (pow_pos (Real.cosh_pos t) _)).mpr
  nlinarith only [Real.one_le_cosh t, sq_nonneg (Real.cosh t - 1)]

private theorem sech_sq_add_tanh_sq (t : ℝ) :
    (2 / (Real.exp t + Real.exp (-t))) ^ 2 + Real.tanh t ^ 2 = 1 := by
  rw [Real.tanh_eq_sinh_div_cosh]
  -- The exponential denominator is twice the hyperbolic cosine.
  have hc : Real.exp t + Real.exp (-t) = 2 * Real.cosh t := by rw [Real.cosh_eq]; ring
  rw [hc]
  have ht := (Real.cosh_pos t).ne'
  field_simp
  nlinarith only [Real.cosh_sq_sub_sinh_sq t]

private theorem auxProfit_sech (E : Environment) (hE : OnUnit E) {lam : ℝ} (hlam : 0 < lam)
    {x : ℝ × ℝ} (hx : x ∈ intT) :
    auxProfit E lam x =
      mu E x * (2 / (Real.exp (Real.log (lam / balance E x)) +
        Real.exp (-Real.log (lam / balance E x)))) ^ 2 := by
  obtain ⟨hs, hb⟩ := intT_cdf_pos E hE hx
  have hl := balance_pos E hE hx
  have hsq := balance_sq E hE hx
  let t := Real.log (lam / balance E x)
  have he : Real.exp t + Real.exp (-t) = lam / balance E x + balance E x / lam := by
    rw [Real.exp_neg, show Real.exp t = lam / balance E x from Real.exp_log (div_pos hlam hl),
      inv_div]
  have hdivide :
      balance E x ^ 2 / E.cdfS x.1 = (1 - E.cdfB x.2)⁻¹ := by
    rw [hsq]
    field_simp [hs.ne']
  have hinv :
      lam / E.cdfS x.1 + lam⁻¹ / (1 - E.cdfB x.2) =
        balance E x / E.cdfS x.1 * (Real.exp t + Real.exp (-t)) := by
    rw [he, mul_add]
    congr 1
    · field_simp
    · calc
        lam⁻¹ / (1 - E.cdfB x.2) = (balance E x ^ 2 / E.cdfS x.1) / lam := by
          rw [hdivide]
          ring
        _ = balance E x / E.cdfS x.1 * (balance E x / lam) := by ring
  have hnorm : (balance E x / E.cdfS x.1) ^ 2 = (E.cdfS x.1 * (1 - E.cdfB x.2))⁻¹ := by
    calc
      (balance E x / E.cdfS x.1) ^ 2 =
          (balance E x ^ 2 / E.cdfS x.1) / E.cdfS x.1 := by ring
      _ = _ := by rw [hdivide, mul_inv]; ring
  change auxProfit E lam x = mu E x * (2 / (Real.exp t + Real.exp (-t))) ^ 2
  rw [auxProfit, hinv, mul_pow, hnorm, mu_formula, P_factor E hE (intT_subset_unitSq hx),
    inv_mul_eq_div, div_div_eq_mul_div, div_pow]
  ring

private theorem auxProfit_tanh_gap (E : Environment) (hE : OnUnit E) {lam : ℝ}
    (hlam : 0 < lam) {x : ℝ × ℝ} (hx : x ∈ intT) :
    mu E x - auxProfit E lam x = mu E x * Real.tanh (Real.log (lam / balance E x)) ^ 2 := by
  rw [auxProfit_sech E hE hlam hx]
  have he := sech_sq_add_tanh_sq (Real.log (lam / balance E x))
  nlinarith only [congrArg (fun t => mu E x * t) he]

private theorem auxProfit_values (E : Environment) (hE : OnUnit E) {lam : ℝ} (hlam : 0 < lam)
    {x : ℝ × ℝ} (hx : x ∈ intT) :
    0 ≤ mu E x - auxProfit E lam x ∧
    mu E x - auxProfit E lam x ≤ mu E x * Real.log (lam / balance E x) ^ 2 ∧
    0 < auxProfit E lam x ∧ auxProfit E lam x ≤ mu E x ∧
    auxProfit E (balance E x) x = mu E x := by
  have hmu := ((onUnit_facts E hE).2.2.1 x (intT_subset_unitSq hx)).mpr hx
  have he := auxProfit_tanh_gap E hE hlam hx
  have hg : 0 ≤ mu E x - auxProfit E lam x := he.symm ▸ mul_nonneg hmu.le (sq_nonneg _)
  refine ⟨hg, ?_, auxProfit_pos E hE hlam hx, sub_nonneg.mp hg, ?_⟩
  · rw [he]
    let t := Real.log (lam / balance E x)
    have hd : |Real.tanh t| ≤ |t| := by
      simpa [Real.dist_eq] using tanh_lipschitz.dist_le_mul t 0
    apply mul_le_mul_of_nonneg_left _ hmu.le
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg (Real.tanh t)) hd 2
  · have hb := balance_pos E hE hx
    have ht := auxProfit_tanh_gap E hE hb hx
    rw [div_self hb.ne', Real.log_one, Real.tanh_zero] at ht
    linarith

private theorem auxProfit_perturbation (E : Environment) (hE : OnUnit E) {lam : ℝ} (hlam : 0 < lam)
    {x : ℝ × ℝ} (hx : x ∈ intT) (θ : ℝ) :
    muStar E - auxProfit E (lam * Real.exp θ) x ≤
      2 * (muStar E - auxProfit E lam x) + 2 * muStar E * θ ^ 2 := by
  let t := Real.log (lam / balance E x)
  have hb := balance_pos E hE hx
  have hmu := ((onUnit_facts E hE).2.2.1 x (intT_subset_unitSq hx)).mpr hx
  have hmuStar := mu_le_muStar E hE (intT_subset_unitSq hx)
  have he : Real.log ((lam * Real.exp θ) / balance E x) = t + θ := by
    rw [mul_div_right_comm, Real.log_mul (div_pos hlam hb).ne' (Real.exp_pos _).ne', Real.log_exp]
  have hgap := auxProfit_tanh_gap E hE (mul_pos hlam (Real.exp_pos θ)) hx
  rw [he] at hgap
  have hbase := auxProfit_tanh_gap E hE hlam hx
  change mu E x - auxProfit E lam x = mu E x * Real.tanh t ^ 2 at hbase
  have hdiff : |Real.tanh (t + θ) - Real.tanh t| ≤ |θ| := by
    simpa [Real.dist_eq] using tanh_lipschitz.dist_le_mul (t + θ) t
  have hsq : (Real.tanh (t + θ) - Real.tanh t)^2 ≤ θ^2 := by
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) hdiff 2
  have hsq' : Real.tanh (t + θ) ^ 2 ≤ 2 * Real.tanh t ^ 2 + 2 * θ ^ 2 := by
    nlinarith only [hsq, sq_nonneg (Real.tanh (t + θ) - 2 * Real.tanh t)]
  have hquad := mul_le_mul_of_nonneg_left hsq' hmu.le
  have hscale := mul_le_mul_of_nonneg_right hmuStar (sq_nonneg θ)
  linarith only [hgap, hbase, hmuStar, hquad, hscale]

/-- High auxiliary profit bounds the logarithmic displacement of the balance. -/
private theorem auxProfit_implies_balance_bound (E : Environment) (hE : OnUnit E) {lam : ℝ}
    (hlam : 0 < lam) {x : ℝ × ℝ} (hx : x ∈ intT) {d : ℝ} (hd : 0 ≤ d) (hd₁ : d < 1)
    (hr : (1 - d ^ 2) * muStar E ≤ auxProfit E lam x) :
    |Real.log (balance E x / lam)| ≤ Real.artanh d := by
  let t := Real.log (lam / balance E x)
  have hmu := ((onUnit_facts E hE).2.2.1 x (intT_subset_unitSq hx)).mpr hx
  have hmuStar := mu_le_muStar E hE (intT_subset_unitSq hx)
  have hd₂ : 0 ≤ 1 - d ^ 2 := by
    have hh := pow_le_pow_left₀ hd hd₁.le 2
    linarith only [hh]
  have hbase : mu E x - auxProfit E lam x = mu E x * Real.tanh t ^ 2 :=
    auxProfit_tanh_gap E hE hlam hx
  have hbound : Real.tanh t ^ 2 ≤ d ^ 2 := by
    apply le_of_mul_le_mul_left _ hmu
    linarith only [hbase, hr, mul_le_mul_of_nonneg_left hmuStar hd₂]
  rw [← sq_abs (Real.tanh t)] at hbound
  obtain ⟨htl, htr⟩ := abs_le.mp (le_of_pow_le_pow_left₀ (by decide) hd hbound)
  have htu : t ≤ Real.artanh d := by
    rw [← Real.artanh_tanh t]
    exact Real.artanh_le_artanh (Real.neg_one_lt_tanh t) hd₁ htr
  have htl' : -t ≤ Real.artanh d := by
    have hneg : Real.tanh (-t) ≤ d := by rw [Real.tanh_neg]; linarith only [htl]
    rw [← Real.artanh_tanh (-t)]
    exact Real.artanh_le_artanh (Real.neg_one_lt_tanh _) hd₁ hneg
  rw [← inv_div, Real.log_inv]
  exact abs_le.mpr ⟨by linarith only [htu], htl'⟩

/-- The offset interval used to form the regular candidates has a universal numerical bound. -/
private theorem regular_offset_halfwidth :
    0 < Real.artanh (1 / Real.sqrt 2000) ∧ Real.artanh (1 / Real.sqrt 2000) ≤ 1 / 40 := by
  let d := 1 / Real.sqrt 2000
  have hroot : 41 ≤ Real.sqrt 2000 := (Real.le_sqrt (by norm_num) (by norm_num)).2 (by norm_num)
  have hpos : 0 < d := by dsimp [d]; positivity
  have hdu : d ≤ 1 / 41 := one_div_le_one_div_of_le (by norm_num) hroot
  have hdlt : d < 1 := by linarith only [hdu]
  change 0 < Real.artanh d ∧ Real.artanh d ≤ 1 / 40
  refine ⟨Real.artanh_pos ⟨hpos, hdlt⟩, ?_⟩
  have h1 : 0 < 1 - d := sub_pos.mpr hdlt
  have harg : 0 < (1 + d) / (1 - d) := div_pos (by linarith only [hpos]) h1
  rw [Real.artanh_eq_half_log ⟨by linarith only [hpos], hdlt.le⟩]
  have hlog := Real.log_le_sub_one_of_pos harg
  have hquot : (1 + d) / (1 - d) - 1 ≤ 1 / 20 := by
    apply sub_le_iff_le_add.mpr
    apply (div_le_iff₀ h1).mpr
    linarith only [hdu]
  linarith only [hlog, hquot]

end BilateralProfitRegular
end BundlePart001


section BundlePart002


namespace BilateralProfitRegular

open Set MeasureTheory MechanismDesign.BilateralTrade
open scoped Topology

/-- A single reciprocal-convexity argument for an increasing CDF and a decreasing tail.
The sign `d` is `1` for the CDF and `-1` for the tail. Absolute continuity of the primitive
allows pointwise virtual-price monotonicity to be used with its almost-everywhere derivative. -/
private theorem reciprocal_convex_of_virtual
    (G f : ℝ → ℝ) (d : ℝ) (hd : d ^ 2 = 1)
    (hG : ∀ x ∈ Ioo 0 1, 0 < G x) (hf : ∀ x ∈ Ioo 0 1, 0 < f x)
    (ha : AbsolutelyContinuousOnInterval G 0 1)
    (hderiv : ∀ᵐ x ∂volume, x ∈ Ioo 0 1 → HasDerivAt G (d * f x) x)
    (hmono : MonotoneOn (fun x => x + d * G x / f x) (Ioo 0 1)) :
    ConvexOn ℝ (Ioo 0 1) (fun x => 1 / G x) := by
  let V (x : ℝ) := x + d * G x / f x
  have hV : MonotoneOn V (Ioo 0 1) := hmono
  have htangent (x : ℝ) (hx : x ∈ Ioo 0 1) (y : ℝ) (hy : y ∈ Ioo 0 1) :
      1 / G x - d * f x / (G x)^2 * (y - x) ≤ 1 / G y := by
    let L (t : ℝ) := d * (V x - t)
    let W (t : ℝ) := G t * L t
    have haL : AbsolutelyContinuousOnInterval L 0 1 := by
      have hdiff : ContDiff ℝ 1 L := by unfold L; fun_prop
      exact hdiff.contDiffOn.absolutelyContinuousOnInterval
    have haW : AbsolutelyContinuousOnInterval W 0 1 := ha.fun_mul haL
    have hL (t : ℝ) : HasDerivAt L (-d) t := by
      simpa only [L, id_eq, mul_neg, mul_one] using
        (((hasDerivAt_id t).const_sub (V x)).const_mul d)
    have he : ∀ᵐ t ∂volume, t ∈ Ioo 0 1 → deriv W t = f t * (V x - V t) := by
      filter_upwards [hderiv] with t ht htI
      have hw := ((ht htI).mul (hL t)).deriv
      change deriv W t = _ at hw
      rw [hw]
      have hf' := (hf t htI).ne'
      have hterm : f t * (d * G t / f t) = d * G t := by field_simp
      calc
        d * f t * L t + G t * (-d) =
            d^2 * (f t * (V x - t)) - d * G t := by unfold L; ring
        _ = f t * (V x - V t) := by
          rw [hd, one_mul, show V t = t + d * G t / f t from rfl]
          rw [show f t * (V x - (t + d * G t / f t)) =
            f t * (V x - t) - f t * (d * G t / f t) from by ring, hterm]
    have hint {a b : ℝ} (ha' : a ∈ Ioo 0 1) (hb' : b ∈ Ioo 0 1) (hab : a ≤ b) :
        ∫ t in a..b, deriv W t = W b - W a := by
      apply (haW.mono _).integral_deriv_eq_sub
      rw [uIcc_of_le hab, uIcc_of_le zero_le_one]
      exact Icc_subset_Icc ha'.1.le hb'.2.le
    have hW : W y ≤ W x := by
      rcases le_total y x with hyx | hxy
      · have hn : 0 ≤ ∫ t in y..x, deriv W t := by
          apply intervalIntegral.integral_nonneg_of_ae_restrict hyx
          rw [Filter.EventuallyLE, ae_restrict_iff' measurableSet_Icc]
          filter_upwards [he] with t ht htI
          have ht' : t ∈ Ioo 0 1 := ⟨hy.1.trans_le htI.1, htI.2.trans_lt hx.2⟩
          change 0 ≤ deriv W t
          rw [ht ht']
          exact mul_nonneg (hf t ht').le (sub_nonneg.mpr (hV ht' hx htI.2))
        rw [hint hy hx hyx] at hn
        exact sub_nonneg.mp hn
      · have hn : 0 ≤ ∫ t in x..y, -deriv W t := by
          apply intervalIntegral.integral_nonneg_of_ae_restrict hxy
          rw [Filter.EventuallyLE, ae_restrict_iff' measurableSet_Icc]
          filter_upwards [he] with t ht htI
          have ht' : t ∈ Ioo 0 1 := ⟨hx.1.trans_le htI.1, htI.2.trans_lt hy.2⟩
          change 0 ≤ -deriv W t
          rw [ht ht']
          exact neg_nonneg.mpr (mul_nonpos_of_nonneg_of_nonpos (hf t ht').le
            (sub_nonpos.mpr (hV hx ht' htI.1)))
        rw [intervalIntegral.integral_neg, hint hx hy hxy] at hn
        linarith only [hn]
    have hfactor (t : ℝ) : L t = G x / f x - d * (t - x) := by
      unfold L V
      calc
        d * (x + d * G x / f x - t) = d^2 * (G x / f x) - d * (t - x) := by ring
        _ = _ := by rw [hd, one_mul]
    have hx' := hG x hx
    have hy' := hG y hy
    have hf' := hf x hx
    have hscaled := mul_le_mul_of_nonneg_right hW hf'.le
    change G y * L y * f x ≤ G x * L x * f x at hscaled
    rw [hfactor, hfactor, sub_self, mul_zero, sub_zero] at hscaled
    have hh : G x / f x * f x = G x := div_mul_cancel₀ _ hf'.ne'
    calc
      1 / G x - d * f x / G x ^ 2 * (y - x) =
          (G x - d * (y - x) * f x) / G x ^ 2 := by
        field_simp [hx'.ne']
      _ ≤ 1 / G y := by
        apply (div_le_div_iff₀ (pow_pos hx' _) hy').mpr
        calc
          (G x - d * (y - x) * f x) * G y = G y * (G x / f x - d * (y - x)) * f x := by
            field_simp [hf'.ne']
          _ ≤ G x * (G x / f x) * f x := hscaled
          _ = 1 * G x ^ 2 := by rw [mul_assoc, hh]; ring
  refine ⟨convex_Ioo _ _, ?_⟩
  intro x hx y hy a b ha' hb' hab
  let z := a * x + b * y
  have hz : z ∈ Ioo 0 1 := (convex_Ioo (0 : ℝ) 1) hx hy ha' hb' hab
  have hzx := mul_le_mul_of_nonneg_left (htangent z hz x hx) ha'
  have hzy := mul_le_mul_of_nonneg_left (htangent z hz y hy) hb'
  change 1 / G z ≤ a * (1 / G x) + b * (1 / G y)
  calc
    1 / G z =
        a * (1 / G z - d * f z / G z ^ 2 * (x - z)) +
          b * (1 / G z - d * f z / G z ^ 2 * (y - z)) := by
      have he : a * (x - z) + b * (y - z) = 0 := by
        calc
          a * (x - z) + b * (y - z) = (a * x + b * y) - (a + b) * z := by ring
          _ = 0 := by rw [hab, one_mul]; exact sub_self z
      linear_combination -(1 / G z) * hab + d * f z / G z ^ 2 * he
    _ ≤ _ := add_le_add hzx hzy

private theorem cdfS_reciprocal_convex (E : Environment) (hE : RegularUnit E) :
    ConvexOn ℝ (Ioo 0 1) (fun p => 1 / E.cdfS p) := by
  have hf : IntervalIntegrable E.fS volume 0 1 := by
    simpa only [hE.1.1, hE.1.2.1] using E.fS_intervalIntegrable
  have hc : E.cdfS = fun x => ∫ t in 0..x, E.fS t := by
    funext x
    rw [Environment.cdfS, hE.1.1]
  have ha : AbsolutelyContinuousOnInterval E.cdfS 0 1 := by
    rw [hc]
    exact hf.absolutelyContinuousOnInterval_intervalIntegral left_mem_uIcc
  refine reciprocal_convex_of_virtual E.cdfS E.fS 1 (by norm_num)
    (fun x hx => cdfS_pos E hE.1 ⟨hx.1, hx.2.le⟩) ?_ ha ?_ ?_
  · intro x hx
    exact E.fS_pos x (by rw [hE.1.1, hE.1.2.1]; exact Ioo_subset_Icc_self hx)
  · rw [hc]
    filter_upwards [hf.ae_hasDerivAt_integral] with x hx hx'
    simpa only [one_mul] using
      hx (by rw [uIcc_of_le zero_le_one]; exact Ioo_subset_Icc_self hx') 0 left_mem_uIcc
  · have hm := hE.2.1
    rw [hE.1.1, hE.1.2.1] at hm
    intro x hx y hy hxy
    simp only [one_mul]
    exact hm (Ioo_subset_Icc_self hx) (Ioo_subset_Icc_self hy) hxy

private theorem tailB_reciprocal_convex (E : Environment) (hE : RegularUnit E) :
    ConvexOn ℝ (Ioo 0 1) (fun q => 1 / (1 - E.cdfB q)) := by
  have hf : IntervalIntegrable E.fB volume 0 1 := by
    simpa only [hE.1.2.2.1, hE.1.2.2.2] using E.fB_intervalIntegrable
  have hc : E.cdfB = fun x => ∫ t in 0..x, E.fB t := by
    funext x
    rw [Environment.cdfB, hE.1.2.2.1]
  have ha : AbsolutelyContinuousOnInterval E.cdfB 0 1 := by
    rw [hc]
    exact hf.absolutelyContinuousOnInterval_intervalIntegral left_mem_uIcc
  have hconst : AbsolutelyContinuousOnInterval (fun _ : ℝ => (1 : ℝ)) 0 1 :=
    (contDiff_const : ContDiff ℝ 1 (fun _ : ℝ => (1 : ℝ))).contDiffOn.absolutelyContinuousOnInterval
  refine reciprocal_convex_of_virtual (fun q => 1 - E.cdfB q) E.fB (-1) (by norm_num)
    (fun x hx => tailB_pos E hE.1 ⟨hx.1.le, hx.2⟩) ?_ (hconst.sub ha) ?_ ?_
  · intro x hx
    exact E.fB_pos x (by rw [hE.1.2.2.1, hE.1.2.2.2]; exact Ioo_subset_Icc_self hx)
  · rw [hc]
    filter_upwards [hf.ae_hasDerivAt_integral] with x hx hx'
    have hd := hx (by rw [uIcc_of_le zero_le_one]; exact Ioo_subset_Icc_self hx') 0 left_mem_uIcc
    simpa only [neg_mul, one_mul] using hd.const_sub 1
  · have hm := hE.2.2
    rw [hE.1.2.2.1, hE.1.2.2.2] at hm
    intro x hx y hy hxy
    simp only [neg_mul, one_mul, neg_div, ← sub_eq_add_neg]
    exact hm (Ioo_subset_Icc_self hx) (Ioo_subset_Icc_self hy) hxy

end BilateralProfitRegular
end BundlePart002


section BundlePart003



namespace BilateralProfitRegular

open Set MechanismDesign.BilateralTrade

private theorem pos_weighted_add {a b s t : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) (hs : 0 < s) (ht : 0 < t) :
    0 < a * s + b * t := by
  by_cases h : a = 0
  · have hb' : 0 < b := by linarith only [h, hab]
    simpa [h] using mul_pos hb' ht
  · exact add_pos_of_pos_of_nonneg (mul_pos (lt_of_le_of_ne ha (Ne.symm h)) hs)
      (mul_nonneg hb ht.le)

private theorem convex_intT : Convex ℝ intT := by
  intro x hx y hy a b ha hb hab
  refine ⟨pos_weighted_add ha hb hab hx.1 hy.1, ?_, ?_⟩
  · have h := pos_weighted_add ha hb hab (sub_pos.mpr hx.2.1) (sub_pos.mpr hy.2.1)
    change a * x.1 + b * y.1 < a * x.2 + b * y.2
    linarith only [h]
  · have h := pos_weighted_add ha hb hab (sub_pos.mpr hx.2.2) (sub_pos.mpr hy.2.2)
    change a * x.2 + b * y.2 < 1
    linarith only [h, hab]

private theorem weighted_sq_div_le {a b s t X Y : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) (hs : 0 < s) (ht : 0 < t) :
    (a * X + b * Y) ^ 2 / (a * s + b * t) ≤ a * (X ^ 2 / s) + b * (Y ^ 2 / t) := by
  apply (div_le_iff₀ (pos_weighted_add ha hb hab hs ht)).mpr
  apply le_of_mul_le_mul_right _ (mul_pos hs ht)
  have he :
      (a * (X^2 / s) + b * (Y^2 / t)) * (a * s + b * t) * (s * t) -
        (a * X + b * Y)^2 * (s * t) = a * b * (t * X - s * Y)^2 := by
    field_simp [hs.ne', ht.ne']
    ring
  linarith only [he, mul_nonneg (mul_nonneg ha hb) (sq_nonneg (t * X - s * Y))]

private theorem auxProfit_reciprocal_convex (E : Environment) (hE : RegularUnit E) {lam : ℝ}
    (hlam : 0 < lam) : ConvexOn ℝ intT (fun x => 1 / auxProfit E lam x) := by
  let u (x : ℝ × ℝ) := lam / E.cdfS x.1 + lam⁻¹ / (1 - E.cdfB x.2)
  let g (x : ℝ × ℝ) := 4 * (x.2 - x.1)
  have hu {x : ℝ × ℝ} (hx : x ∈ intT) : 0 < u x :=
    add_pos (div_pos hlam (intT_cdf_pos E hE.1 hx).1)
      (div_pos (inv_pos.mpr hlam) (intT_cdf_pos E hE.1 hx).2)
  refine ⟨convex_intT, ?_⟩
  intro x hx y hy a b ha hb hab
  let z := a • x + b • y
  have hz : z ∈ intT := convex_intT hx hy ha hb hab
  have hx₁ : x.1 ∈ Ioo 0 1 := ⟨hx.1, hx.2.1.trans hx.2.2⟩
  have hy₁ : y.1 ∈ Ioo 0 1 := ⟨hy.1, hy.2.1.trans hy.2.2⟩
  have hx₂ : x.2 ∈ Ioo 0 1 := ⟨hx.1.trans hx.2.1, hx.2.2⟩
  have hy₂ : y.2 ∈ Ioo 0 1 := ⟨hy.1.trans hy.2.1, hy.2.2⟩
  have hCs := (cdfS_reciprocal_convex E hE).2 hx₁ hy₁ ha hb hab
  have hCb := (tailB_reciprocal_convex E hE).2 hx₂ hy₂ ha hb hab
  change 1 / E.cdfS z.1 ≤ a * (1 / E.cdfS x.1) + b * (1 / E.cdfS y.1) at hCs
  change 1 / (1 - E.cdfB z.2) ≤
    a * (1 / (1 - E.cdfB x.2)) + b * (1 / (1 - E.cdfB y.2)) at hCb
  have huc : u z ≤ a * u x + b * u y := by
    have hS := mul_le_mul_of_nonneg_left hCs hlam.le
    have hB := mul_le_mul_of_nonneg_left hCb (inv_nonneg.mpr hlam.le)
    dsimp only [u]
    simp only [div_eq_mul_inv, one_mul] at hS hB ⊢
    linarith only [hS, hB]
  have gpos {x : ℝ × ℝ} (hx : x ∈ intT) : 0 < g x :=
    mul_pos (by norm_num) (sub_pos.mpr hx.2.1)
  have hg : g z = a * g x + b * g y := by
    change 4 * ((a * x.2 + b * y.2) - (a * x.1 + b * y.1)) = _
    unfold g
    ring
  have he (w : ℝ × ℝ) : 1 / auxProfit E lam w = u w ^ 2 / g w := by
    simp only [auxProfit, one_div, inv_div, u, g]
  change 1 / auxProfit E lam z ≤ a * (1 / auxProfit E lam x) + b * (1 / auxProfit E lam y)
  simp only [he]
  calc
    u z ^ 2 / g z ≤ (a * u x + b * u y) ^ 2 / g z :=
      div_le_div_of_nonneg_right (pow_le_pow_left₀ (hu hz).le huc 2) (gpos hz).le
    _ ≤ _ := by rw [hg]; exact weighted_sq_div_le ha hb hab (gpos hx) (gpos hy)

private theorem lemma_6_2 (E : Environment) (hE : RegularUnit E) (lam : ℝ) (hlam : 0 < lam) :
    ConvexOn ℝ intT (fun x => 1 / auxProfit E lam x) ∧
    ∀ x ∈ intT,
      auxProfit E lam x =
          mu E x * (2 / (Real.exp (Real.log (lam / balance E x)) +
            Real.exp (-Real.log (lam / balance E x)))) ^ 2 ∧
        0 ≤ mu E x - auxProfit E lam x ∧
        mu E x - auxProfit E lam x ≤ mu E x * Real.log (lam / balance E x) ^ 2 ∧
        0 < auxProfit E lam x ∧ auxProfit E lam x ≤ mu E x ∧
        auxProfit E (balance E x) x = mu E x ∧
        ∀ θ : ℝ, muStar E - auxProfit E (lam * Real.exp θ) x ≤
          2 * (muStar E - auxProfit E lam x) + 2 * muStar E * θ ^ 2 := by
  refine ⟨auxProfit_reciprocal_convex E hE hlam, ?_⟩
  intro x hx
  obtain ⟨h₁, h₂, h₃, h₄, h₅⟩ := auxProfit_values E hE.1 hlam hx
  exact ⟨auxProfit_sech E hE.1 hlam hx, h₁, h₂, h₃, h₄, h₅,
    auxProfit_perturbation E hE.1 hlam hx⟩

/-- A common lower bound on auxiliary profit persists over the convex hull. -/
private theorem auxProfit_lower_convexHull (E : Environment) (hE : RegularUnit E) {lam : ℝ}
    (hlam : 0 < lam) {S : Set (ℝ × ℝ)} (hS : S ⊆ intT) {r : ℝ} (hr : 0 < r)
    (h : ∀ x ∈ S, r ≤ auxProfit E lam x) :
    ∀ x ∈ convexHull ℝ S, x ∈ intT ∧ r ≤ auxProfit E lam x := by
  have hs : S ⊆ {x ∈ intT | 1 / auxProfit E lam x ≤ 1 / r} := by
    intro x hx
    exact ⟨hS hx, one_div_le_one_div_of_le hr (h x hx)⟩
  have hsub := convexHull_min hs ((auxProfit_reciprocal_convex E hE hlam).convex_le (1 / r))
  intro x hx
  obtain ⟨hxi, hxv⟩ := hsub hx
  exact ⟨hxi, le_of_one_div_le_one_div (auxProfit_pos E hE.1 hlam hxi) hxv⟩

end BilateralProfitRegular
end BundlePart003

open BilateralProfitRegular
open MechanismDesign.BilateralTrade

theorem solution (E : Environment) (hE : RegularUnit E) (lam : ℝ) (hlam : 0 < lam) :
    ConvexOn ℝ intT (fun x => 1 / auxProfit E lam x) ∧
    ∀ x ∈ intT,
      auxProfit E lam x =
          mu E x * (2 / (Real.exp (Real.log (lam / balance E x)) +
            Real.exp (-Real.log (lam / balance E x)))) ^ 2 ∧
        0 ≤ mu E x - auxProfit E lam x ∧
        mu E x - auxProfit E lam x ≤ mu E x * Real.log (lam / balance E x) ^ 2 ∧
        0 < auxProfit E lam x ∧ auxProfit E lam x ≤ mu E x ∧
        auxProfit E (balance E x) x = mu E x ∧
        ∀ θ : ℝ, muStar E - auxProfit E (lam * Real.exp θ) x ≤
          2 * (muStar E - auxProfit E lam x) + 2 * muStar E * θ ^ 2 := by
  exact BilateralProfitRegular.lemma_6_2 E hE lam hlam
