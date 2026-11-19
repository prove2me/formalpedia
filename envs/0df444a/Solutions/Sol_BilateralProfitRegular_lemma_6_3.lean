-- Prove2me | solution 1 for BilateralProfitRegular.lemma_6_3
-- status  : ACCEPTED   (prove)
-- author  : @sim2000dg
-- created : 2026-11-18T15:24:00.946828+00:00
-- url     : https://prove2.me/submissions/a4105ff8-1b34-4aa1-8a0c-28ed21728474

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

open Set MechanismDesign.BilateralTrade

private theorem lemma_6_3 (E : Environment) (hE : RegularUnit E) (lam : ℝ) (hlam : 0 < lam)
    (x z : ℝ × ℝ) (hx : x ∈ intT) (hz : z ∈ intT)
    (hrx : 99 / 100 * muStar E ≤ auxProfit E lam x)
    (hrz : 99 / 100 * muStar E ≤ auxProfit E lam z) :
    (x.1, z.2) ∈ triT ∧ (z.1, x.2) ∈ triT ∧
    muStar E - mu E (x.1, z.2) ≤
      4 * (muStar E - auxProfit E lam x + (muStar E - auxProfit E lam z)) ∧
    muStar E - mu E (z.1, x.2) ≤
      4 * (muStar E - auxProfit E lam x + (muStar E - auxProfit E lam z)) ∧
    ∀ a ∈ ({x, z, (x.1, z.2), (z.1, x.2)} : Set (ℝ × ℝ)),
      ∀ b ∈ ({x, z, (x.1, z.2), (z.1, x.2)} : Set (ℝ × ℝ)), P E a ≤ 3 * P E b := by
  let M := muStar E
  have hM : 0 < M := (onUnit_facts E hE.1).2.2.2.1.1
  let A (t : ℝ × ℝ) := lam / E.cdfS t.1
  let B (t : ℝ × ℝ) := lam⁻¹ / (1 - E.cdfB t.2)
  let H (t : ℝ × ℝ) := (A t + B t) / 2
  let D (t : ℝ × ℝ) := (A t - B t) / 2
  let Δ (t : ℝ × ℝ) := M - auxProfit E lam t
  have hA {t : ℝ × ℝ} (ht : t ∈ intT) : 0 < A t :=
    div_pos hlam (intT_cdf_pos E hE.1 ht).1
  have hB {t : ℝ × ℝ} (ht : t ∈ intT) : 0 < B t :=
    div_pos (inv_pos.mpr hlam) (intT_cdf_pos E hE.1 ht).2
  have hH {t : ℝ × ℝ} (ht : t ∈ intT) : 0 < H t :=
    div_pos (add_pos (hA ht) (hB ht)) (by norm_num)
  have hmem {s t : ℝ × ℝ} (hs : s ∈ intT) (ht : t ∈ intT) :
      (s.1, t.2) ∈ BilateralProfitMHR.unitSq :=
    ⟨(intT_subset_unitSq hs).1, (intT_subset_unitSq ht).2⟩
  have hP {s t : ℝ × ℝ} (hs : s ∈ intT) (ht : t ∈ intT) :
      P E (s.1,t.2) * (A s * B t) = 1 := by
    rw [P_factor E hE.1 (hmem hs ht)]
    dsimp [A, B]
    have hs' := (intT_cdf_pos E hE.1 hs).1.ne'
    have ht' := (intT_cdf_pos E hE.1 ht).2.ne'
    field_simp [hlam.ne']
  have hPpos {s t : ℝ × ℝ} (hs : s ∈ intT) (ht : t ∈ intT) :
      0 < P E (s.1,t.2) := by
    rw [P_factor E hE.1 (hmem hs ht)]
    exact mul_pos (intT_cdf_pos E hE.1 hs).1 (intT_cdf_pos E hE.1 ht).2
  have hspread {t : ℝ × ℝ} (ht : t ∈ intT) :
      auxProfit E lam t * H t ^ 2 = t.2 - t.1 := by
    change (4 * (t.2 - t.1) / (A t + B t) ^ 2) * ((A t + B t) / 2) ^ 2 = _
    have hp := (add_pos (hA ht) (hB ht)).ne'
    field_simp
    ring
  have hdev {t : ℝ × ℝ} (ht : t ∈ intT) : M * D t ^ 2 ≤ Δ t * H t ^ 2 := by
    have hh := mul_le_mul_of_nonneg_right (mu_le_muStar E hE.1 (intT_subset_unitSq ht))
      (mul_pos (hA ht) (hB ht)).le
    rw [mu_formula, mul_assoc, hP ht ht, mul_one] at hh
    have he : A t * B t = H t ^ 2 - D t ^ 2 := by unfold H D; ring
    rw [he, ← hspread ht] at hh
    dsimp [Δ]
    linarith only [hh]
  have hΔ {t : ℝ × ℝ} (ht : t ∈ intT) : 0 ≤ Δ t :=
    nonneg_of_mul_nonneg_left
      ((mul_nonneg hM.le (sq_nonneg _)).trans (hdev ht)) (pow_pos (hH ht) _)
  have hbds {t : ℝ × ℝ} (ht : t ∈ intT) (hr : 99 / 100 * M ≤ auxProfit E lam t) :
      9 / 10 * H t ≤ A t ∧ A t ≤ 11 / 10 * H t ∧
      9 / 10 * H t ≤ B t ∧ B t ≤ 11 / 10 * H t := by
    have hd : Δ t ≤ M / 100 := by dsimp [Δ]; linarith
    have hs := (hdev ht).trans (mul_le_mul_of_nonneg_right hd (sq_nonneg (H t)))
    have hh : D t ^ 2 ≤ (H t / 10) ^ 2 := by
      apply le_of_mul_le_mul_left _ hM
      nlinarith only [hs]
    have habs : |D t| ≤ H t / 10 := by
      rw [← sq_abs (D t)] at hh
      exact le_of_pow_le_pow_left₀ (by decide) (by linarith only [hH ht]) hh
    obtain ⟨hl, hu⟩ := abs_le.mp habs
    unfold D H at hl hu
    unfold H
    exact ⟨by linarith, by linarith, by linarith, by linarith⟩
  let G (s t : ℝ × ℝ) := M - mu E (s.1,t.2)
  have hG {s t : ℝ × ℝ} (hs : s ∈ intT) (ht : t ∈ intT) : 0 ≤ G s t :=
    sub_nonneg.mpr (mu_le_muStar E hE.1 (hmem hs ht))
  have hG_eq {s t : ℝ × ℝ} (hs : s ∈ intT) (ht : t ∈ intT) :
      G s t * (A s * B t) = M * (A s * B t) - (t.2 - s.1) := by
    change (M - mu E (s.1,t.2)) * _ = _
    rw [sub_mul, mu_formula, mul_assoc, hP hs ht, mul_one]
  let S := G x z * (A x * B z) + G z x * (A z * B x)
  have hS0 : 0 ≤ S := add_nonneg (mul_nonneg (hG hx hz) (mul_pos (hA hx) (hB hz)).le)
    (mul_nonneg (hG hz hx) (mul_pos (hA hz) (hB hx)).le)
  have hS :
      S = Δ x * H x ^ 2 + Δ z * H z ^ 2 - M * (H x - H z) ^ 2 - 2 * M * D x * D z := by
    unfold S
    rw [hG_eq hx hz, hG_eq hz hx]
    have he : (z.2 - x.1) + (x.2 - z.1) = (x.2 - x.1) + (z.2 - z.1) := by ring
    rw [sub_add_sub_comm, he, ← hspread hx, ← hspread hz]
    unfold Δ D H
    ring
  have hcross : -(2 * M * D x * D z) ≤ M * D x ^ 2 + M * D z ^ 2 := by
    nlinarith only [mul_nonneg hM.le (sq_nonneg (D x + D z))]
  let m := max (H x) (H z)
  have hm : 0 < m := (hH hx).trans_le (le_max_left _ _)
  have hm₁ : H x ≤ m := le_max_left _ _
  have hm₂ : H z ≤ m := le_max_right _ _
  have hΔm : Δ x + Δ z ≤ M / 50 := by dsimp [Δ]; linarith only [hrx, hrz]
  have hSle : S ≤ 2 * (Δ x + Δ z) * m ^ 2 - M * (H x - H z) ^ 2 := by
    have hh₁ : H x ^ 2 ≤ m ^ 2 := pow_le_pow_left₀ (hH hx).le hm₁ 2
    have hh₂ : H z ^ 2 ≤ m ^ 2 := pow_le_pow_left₀ (hH hz).le hm₂ 2
    rw [hS]
    linarith only [hcross, hdev hx, hdev hz, mul_le_mul_of_nonneg_left hh₁ (hΔ hx),
      mul_le_mul_of_nonneg_left hh₂ (hΔ hz)]
  have hdiff : |H x - H z| ≤ m / 5 := by
    have hb := mul_le_mul_of_nonneg_right hΔm (sq_nonneg m)
    have ht : (H x - H z)^2 ≤ (m / 5)^2 := by
      apply le_of_mul_le_mul_left _ hM
      nlinarith only [hS0, hSle, hb]
    rw [← sq_abs (H x - H z)] at ht
    exact le_of_pow_le_pow_left₀ (by decide) (by linarith only [hm]) ht
  obtain ⟨hmd₁, hmd₂⟩ := abs_le.mp hdiff
  have hmin₁ : 4 / 5 * m ≤ H x := by
    dsimp [m] at hmd₁ ⊢
    rcases le_total (H x) (H z) with h | h
    · rw [max_eq_right h] at hmd₁ ⊢
      linarith only [hmd₁]
    · rw [max_eq_left h]
      linarith only [hH hx]
  have hmin₂ : 4 / 5 * m ≤ H z := by
    dsimp [m] at hmd₂ ⊢
    rcases le_total (H x) (H z) with h | h
    · rw [max_eq_right h]
      linarith only [hH hz]
    · rw [max_eq_left h] at hmd₂ ⊢
      linarith only [hmd₂]
  have hprod : 4 / 5 * m ^ 2 ≤ H x * H z := by
    by_cases h : H x ≤ H z
    · have he : m = H z := max_eq_right h
      calc
        (4 / 5) * m ^ 2 = (4 / 5 * m) * H z := by rw [he]; ring
        _ ≤ H x * H z := mul_le_mul_of_nonneg_right hmin₁ (hH hz).le
    · have he : m = H x := max_eq_left (le_of_not_ge h)
      calc
        (4 / 5) * m ^ 2 = H x * (4 / 5 * m) := by rw [he]; ring
        _ ≤ H x * H z := mul_le_mul_of_nonneg_left hmin₂ (hH hx).le
  obtain ⟨hax₁, hax₂, hbx₁, hbx₂⟩ := hbds hx hrx
  obtain ⟨haz₁, haz₂, hbz₁, hbz₂⟩ := hbds hz hrz
  have hab₁ : 16 / 25 * m ^ 2 ≤ A x * B z := by
    have he := mul_le_mul hax₁ hbz₁ (by linarith only [hH hz]) (hA hx).le
    nlinarith only [he, hprod]
  have hab₂ : 16 / 25 * m ^ 2 ≤ A z * B x := by
    have he := mul_le_mul haz₁ hbx₁ (by linarith only [hH hx]) (hA hz).le
    nlinarith only [he, hprod]
  have hGle {s t : ℝ × ℝ} (hs : s ∈ intT) (ht : t ∈ intT)
      (hab : 16 / 25 * m ^ 2 ≤ A s * B t) (hg : G s t * (A s * B t) ≤ S) :
      G s t ≤ 4 * (Δ x + Δ z) := by
    have hlow := mul_le_mul_of_nonneg_left hab (hG hs ht)
    have hpos : 0 < m ^ 2 := pow_pos hm _
    have hd := add_nonneg (hΔ hx) (hΔ hz)
    apply le_of_mul_le_mul_right _ hpos
    nlinarith only [hlow, hg, hSle, mul_nonneg hM.le (sq_nonneg (H x - H z)),
      mul_nonneg hd hpos.le]
  have hG₁ := hGle hx hz hab₁
    (le_add_of_nonneg_right (mul_nonneg (hG hz hx) (mul_pos (hA hz) (hB hx)).le))
  have hG₂ := hGle hz hx hab₂
    (le_add_of_nonneg_left (mul_nonneg (hG hx hz) (mul_pos (hA hx) (hB hz)).le))
  have htri {s t : ℝ × ℝ} (hs : s ∈ intT) (ht : t ∈ intT)
      (hg : G s t ≤ 4 * (Δ x + Δ z)) : (s.1, t.2) ∈ triT := by
    have hp : 0 < mu E (s.1,t.2) := by dsimp [G] at hg; linarith only [hM, hg, hΔm]
    exact ⟨hs.1.le, le_of_lt ((onUnit_facts E hE.1).2.2.1 _ (hmem hs ht) |>.mp hp).2.1,
      ht.2.2.le⟩
  refine ⟨htri hx hz hG₁, htri hz hx hG₂, hG₁, hG₂, ?_⟩
  have hProb {s t : ℝ × ℝ} (hs : s ∈ intT) (ht : t ∈ intT)
      (ha₁ : 9 / 10 * H s ≤ A s) (ha₂ : A s ≤ 11 / 10 * H s)
      (hb₁ : 9 / 10 * H t ≤ B t) (hb₂ : B t ≤ 11 / 10 * H t)
      (hm_s : 4 / 5 * m ≤ H s) (hm_t : 4 / 5 * m ≤ H t)
      (hs_m : H s ≤ m) (ht_m : H t ≤ m) :
      1 / ((11 / 10 * m) ^ 2) ≤ P E (s.1,t.2) ∧
        P E (s.1,t.2) ≤ 1 / ((18 / 25 * m) ^ 2) := by
    have hloA : 18 / 25 * m ≤ A s := by linarith only [ha₁, hm_s]
    have hloB : 18 / 25 * m ≤ B t := by linarith only [hb₁, hm_t]
    have hhiA : A s ≤ 11 / 10 * m := by linarith only [ha₂, hs_m]
    have hhiB : B t ≤ 11 / 10 * m := by linarith only [hb₂, ht_m]
    have he := hP hs ht
    have hv := (hPpos hs ht).le
    constructor
    · have hbound := mul_le_mul hhiA hhiB (hB ht).le (by linarith only [hm])
      apply (div_le_iff₀ (pow_pos (by linarith only [hm] : 0 < 11 / 10 * m) _)).mpr
      simpa only [sq, mul_comm (P E (s.1,t.2))] using
        he.symm.le.trans (mul_le_mul_of_nonneg_left hbound hv)
    · have hbound := mul_le_mul hloA hloB (by linarith only [hm]) (hA hs).le
      apply (le_div_iff₀ (pow_pos (by linarith only [hm] : 0 < 18 / 25 * m) _)).mpr
      simpa only [sq] using
        (mul_le_mul_of_nonneg_left hbound hv).trans he.le
  have hPall (a : ℝ × ℝ) (ha : a ∈ ({x, z, (x.1, z.2), (z.1, x.2)} : Set (ℝ × ℝ))) :
      1 / ((11 / 10 * m) ^ 2) ≤ P E a ∧ P E a ≤ 1 / ((18 / 25 * m) ^ 2) := by
    simp only [mem_insert_iff, mem_singleton_iff] at ha
    rcases ha with rfl | rfl | rfl | rfl
    · exact hProb hx hx hax₁ hax₂ hbx₁ hbx₂ hmin₁ hmin₁ hm₁ hm₁
    · exact hProb hz hz haz₁ haz₂ hbz₁ hbz₂ hmin₂ hmin₂ hm₂ hm₂
    · exact hProb hx hz hax₁ hax₂ hbz₁ hbz₂ hmin₁ hmin₂ hm₁ hm₂
    · exact hProb hz hx haz₁ haz₂ hbx₁ hbx₂ hmin₂ hmin₁ hm₂ hm₁
  intro a ha b hb
  apply (hPall a ha).2.trans
  apply le_trans _ (mul_le_mul_of_nonneg_left (hPall b hb).1 (by norm_num))
  rw [mul_one_div]
  apply (div_le_div_iff₀ (pow_pos (by linarith only [hm] : 0 < 18 / 25 * m) _)
    (pow_pos (by linarith only [hm] : 0 < 11 / 10 * m) _)).mpr
  nlinarith only [sq_nonneg m]

end BilateralProfitRegular
end BundlePart001

open BilateralProfitRegular
open MechanismDesign.BilateralTrade

theorem solution (E : Environment) (hE : RegularUnit E) (lam : ℝ) (hlam : 0 < lam)
    (x z : ℝ × ℝ) (hx : x ∈ intT) (hz : z ∈ intT)
    (hrx : 99 / 100 * muStar E ≤ auxProfit E lam x)
    (hrz : 99 / 100 * muStar E ≤ auxProfit E lam z) :
    (x.1, z.2) ∈ triT ∧ (z.1, x.2) ∈ triT ∧
    muStar E - mu E (x.1, z.2) ≤
      4 * (muStar E - auxProfit E lam x + (muStar E - auxProfit E lam z)) ∧
    muStar E - mu E (z.1, x.2) ≤
      4 * (muStar E - auxProfit E lam x + (muStar E - auxProfit E lam z)) ∧
    ∀ a ∈ ({x, z, (x.1, z.2), (z.1, x.2)} : Set (ℝ × ℝ)),
      ∀ b ∈ ({x, z, (x.1, z.2), (z.1, x.2)} : Set (ℝ × ℝ)), P E a ≤ 3 * P E b := by
  exact BilateralProfitRegular.lemma_6_3 E hE lam hlam x z hx hz hrx hrz
