-- Prove2me | solution 1 for CrowdSignal.OnePrice.lemma_3_iii
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-22T18:03:54.886982+00:00
-- url     : https://prove2.me/submissions/9a91bf3f-6f71-49aa-b0f2-17e4b83cb3bc

import Mathlib
import Definitions.Def_CrowdSignal_OnePrice_Setting

namespace CSOP1Aux
open CrowdSignal.OnePrice

/-- normalized conditional regular profit (p2 = qi*y, r = p1/qj) -/
noncomputable def kk (a r y : ℝ) : ℝ :=
  if y < r then a * y + (1 - a) * (1 - y) * y else (a / (1 - r) + (1 - a)) * (1 - y) * y

noncomputable def rho (a r : ℝ) : ℝ :=
  if r ≤ 1 / 2 then (a / (1 - r) + (1 - a)) / 4
  else if 2 * (1 - a) * r ≤ 1 then r * (1 - (1 - a) * r) else 1 / (4 * (1 - a))

noncomputable def ys (a r : ℝ) : ℝ :=
  if r ≤ 1 / 2 then 1 / 2 else if 2 * (1 - a) * r ≤ 1 then r else 1 / (2 * (1 - a))

noncomputable def phi (a r : ℝ) : ℝ := (1 - r) * rho a r

lemma kk_le (a r y : ℝ) (ha0 : 0 < a) (ha1 : a < 1) (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hy0 : 0 < y) (hy1 : y ≤ 1) : kk a r y ≤ rho a r := by
  have h1r : 0 < 1 - r := by linarith
  set K := a / (1 - r) with hKdef
  have hK : K * (1 - r) = a := by rw [hKdef]; field_simp
  have hKpos : 0 < K := div_pos ha0 h1r
  have hb : 0 < 1 - a := by linarith
  unfold kk rho
  split_ifs with hyr hr2 hr3 hr2 hr3
  · -- y < r, r ≤ 1/2
    have h1 : a * y ≤ K * (1 - y) * y := by
      have : a ≤ K * (1 - y) := by rw [← hK]; nlinarith
      nlinarith
    have h2 : (1 - y) * y ≤ 1 / 4 := by nlinarith [sq_nonneg (y - 1/2)]
    have h3 := mul_le_mul_of_nonneg_left h2 hKpos.le
    have h4 := mul_le_mul_of_nonneg_left h2 hb.le
    have e : (K + (1 - a)) * (1 - y) * y = K * ((1 - y) * y) + (1 - a) * ((1 - y) * y) := by ring
    nlinarith
  · -- y < r, case 2
    have h5 : (1 - a) * (r + y) ≤ 1 := by nlinarith
    have h6 : 0 ≤ (r - y) * (1 - (1 - a) * (r + y)) :=
      mul_nonneg (by linarith) (by linarith)
    nlinarith
  · -- y < r, case 3
    have : (2 * (1 - a) * y - 1) ^ 2 ≥ 0 := sq_nonneg _
    rw [le_div_iff₀ (by positivity)]
    nlinarith
  · have h2 : (1 - y) * y ≤ 1 / 4 := by nlinarith [sq_nonneg (y - 1/2)]
    have : 0 ≤ K + (1 - a) := by linarith
    nlinarith
  · have h2 : (1 - y) * y ≤ (1 - r) * r := by nlinarith
    have : 0 ≤ K + (1 - a) := by linarith
    have h3 : (K + (1 - a)) * (1 - y) * y ≤ (K + (1 - a)) * ((1 - r) * r) := by
      rw [mul_assoc]; exact mul_le_mul_of_nonneg_left h2 this
    have h4 : (K + (1 - a)) * ((1 - r) * r) = r * (1 - (1 - a) * r) := by
      have : (K + (1 - a)) * ((1 - r) * r) = (K * (1 - r)) * r + (1 - a) * (1 - r) * r := by ring
      rw [this, hK]; ring
    linarith
  · have hle : K * (1 - y) ≤ a := by rw [← hK]; nlinarith
    have h1 : K * (1 - y) * y ≤ a * y := by nlinarith
    have : (2 * (1 - a) * y - 1) ^ 2 ≥ 0 := sq_nonneg _
    rw [le_div_iff₀ (by positivity)]
    nlinarith

lemma ys_mem (a r : ℝ) (ha0 : 0 < a) (ha1 : a < 1) (hr0 : 0 ≤ r) (hr1 : r < 1) :
    0 < ys a r ∧ ys a r < 1 := by
  unfold ys
  split_ifs with h1 h2
  · norm_num
  · constructor <;> linarith
  · push_neg at h1 h2
    have hb : 0 < 1 - a := by linarith
    constructor
    · positivity
    · rw [div_lt_one (by positivity)]; nlinarith

lemma kk_ys (a r : ℝ) (ha0 : 0 < a) (ha1 : a < 1) (hr0 : 0 ≤ r) (hr1 : r < 1) :
    kk a r (ys a r) = rho a r := by
  have h1r : 0 < 1 - r := by linarith
  have hb : 0 < 1 - a := by linarith
  by_cases h1 : r ≤ 1 / 2
  · have hys : ys a r = 1 / 2 := by unfold ys; rw [if_pos h1]
    rw [hys]; unfold kk rho
    rw [if_neg (by linarith), if_pos h1]; ring
  · by_cases h2 : 2 * (1 - a) * r ≤ 1
    · have hys : ys a r = r := by unfold ys; rw [if_neg h1, if_pos h2]
      rw [hys]; unfold kk rho
      rw [if_neg (lt_irrefl r), if_neg h1, if_pos h2]
      field_simp; ring
    · have hys : ys a r = 1 / (2 * (1 - a)) := by unfold ys; rw [if_neg h1, if_neg h2]
      rw [hys]; unfold kk rho
      have hlt : 1 / (2 * (1 - a)) < r := by
        rw [div_lt_iff₀ (by positivity)]; push_neg at h2; linarith
      rw [if_pos hlt, if_neg h1, if_neg h2]
      field_simp; ring

lemma rho_ge_kk_half (a r : ℝ) (ha0 : 0 < a) (ha1 : a < 1) (hr0 : 0 ≤ r) (hr1 : r < 1) :
    0 < rho a r := by
  have := kk_le a r (1/2) ha0 ha1 hr0 hr1 (by norm_num) (by norm_num)
  have h1r : 0 < 1 - r := by linarith
  have : 0 < kk a r (1/2) := by
    unfold kk
    split_ifs
    · nlinarith
    · have : 0 < a / (1 - r) := div_pos ha0 h1r
      nlinarith
  linarith

lemma phi_pos (a r : ℝ) (ha0 : 0 < a) (ha1 : a < 1) (hr0 : 0 ≤ r) (hr1 : r < 1) :
    0 < phi a r := by
  unfold phi
  have := rho_ge_kk_half a r ha0 ha1 hr0 hr1
  have : 0 < 1 - r := by linarith
  positivity

/-- pointwise strict decrease of (1-r) * kk in r -/
lemma kk_strict (a r1 r2 y : ℝ) (ha0 : 0 < a) (ha1 : a < 1) (hr0 : 0 ≤ r1) (h12 : r1 < r2)
    (hr2 : r2 < 1) (hy0 : 0 < y) (hy1 : y < 1) :
    (1 - r2) * kk a r2 y < (1 - r1) * kk a r1 y := by
  have h1r1 : 0 < 1 - r1 := by linarith
  have h1r2 : 0 < 1 - r2 := by linarith
  have hb : 0 < 1 - a := by linarith
  have e1 : (1 - r1) * (a / (1 - r1) + (1 - a)) = a + (1 - a) * (1 - r1) := by
    field_simp
  have e2 : (1 - r2) * (a / (1 - r2) + (1 - a)) = a + (1 - a) * (1 - r2) := by
    field_simp
  have hf1 : 0 < a * y + (1 - a) * (1 - y) * y := by
    have : 0 < (1 - a) * (1 - y) * y := by
      have : 0 < 1 - y := by linarith
      positivity
    nlinarith
  unfold kk
  split_ifs with hA hB hB
  · nlinarith
  · -- y < r2, r1 ≤ y
    push_neg at hB
    have : (1 - r1) * ((a / (1 - r1) + (1 - a)) * (1 - y) * y)
        = (a + (1 - a) * (1 - r1)) * (1 - y) * y := by
      rw [← e1]; ring
    rw [this]
    have hA' : a + (1 - a) * (1 - y) ≤ a + (1 - a) * (1 - r1) := by nlinarith
    have hpos : 0 < a + (1 - a) * (1 - y) := by nlinarith
    have : (1 - r2) * (a * y + (1 - a) * (1 - y) * y) = (1 - r2) * (a + (1 - a) * (1 - y)) * y := by ring
    rw [this]
    have h3 : (1 - r2) * (a + (1 - a) * (1 - y)) < (1 - y) * (a + (1 - a) * (1 - r1)) := by
      calc (1 - r2) * (a + (1 - a) * (1 - y)) < (1 - y) * (a + (1 - a) * (1 - y)) := by
            apply mul_lt_mul_of_pos_right _ hpos; linarith
        _ ≤ (1 - y) * (a + (1 - a) * (1 - r1)) := by
            apply mul_le_mul_of_nonneg_left hA'; linarith
    nlinarith
  · exfalso; push_neg at hA; linarith
  · push_neg at hA
    have : (1 - r1) * ((a / (1 - r1) + (1 - a)) * (1 - y) * y)
        = (a + (1 - a) * (1 - r1)) * (1 - y) * y := by
      rw [← e1]; ring
    rw [this]
    have : (1 - r2) * ((a / (1 - r2) + (1 - a)) * (1 - y) * y)
        = (a + (1 - a) * (1 - r2)) * (1 - y) * y := by
      rw [← e2]; ring
    rw [this]
    have : 0 < (1 - y) * y := by
      have : 0 < 1 - y := by linarith
      positivity
    have : (1 - a) * (1 - r2) < (1 - a) * (1 - r1) := by nlinarith
    nlinarith

lemma phi_strict (a r1 r2 : ℝ) (ha0 : 0 < a) (ha1 : a < 1) (hr0 : 0 ≤ r1) (h12 : r1 < r2)
    (hr2 : r2 < 1) : phi a r2 < phi a r1 := by
  unfold phi
  obtain ⟨hy0, hy1⟩ := ys_mem a r2 ha0 ha1 (by linarith) hr2
  rw [← kk_ys a r2 ha0 ha1 (by linarith) hr2]
  calc (1 - r2) * kk a r2 (ys a r2) < (1 - r1) * kk a r1 (ys a r2) :=
        kk_strict a r1 r2 _ ha0 ha1 hr0 h12 hr2 hy0 hy1
    _ ≤ (1 - r1) * rho a r1 := by
        apply mul_le_mul_of_nonneg_left _ (by linarith)
        exact kk_le a r1 _ ha0 ha1 hr0 (by linarith) hy0 hy1.le

lemma phi_anti (a r1 r2 : ℝ) (ha0 : 0 < a) (ha1 : a < 1) (hr0 : 0 ≤ r1) (h12 : r1 ≤ r2)
    (hr2 : r2 < 1) : phi a r2 ≤ phi a r1 := by
  rcases h12.lt_or_eq with h | h
  · exact (phi_strict a r1 r2 ha0 ha1 hr0 h hr2).le
  · rw [h]

lemma phi_case1 (a r : ℝ) (hr : r ≤ 1 / 2) : phi a r = (1 - (1 - a) * r) / 4 := by
  unfold phi rho
  rw [if_pos hr]
  have : 1 - r ≠ 0 := by intro h; linarith
  field_simp
  ring


lemma rsProfit_eq (P : Params) (qi qj p1 y : ℝ) (hqi : 0 < qi) (hqj : 0 < qj) :
    rsProfit P qi qj p1 (qi * y) = qi * kk P.α (p1 / qj) y := by
  have hy : qi * y / qi = y := by field_simp
  have hc : (qi * y < p1 * qi / qj) ↔ (y < p1 / qj) := by
    rw [lt_div_iff₀ hqj, lt_div_iff₀ hqj]
    constructor
    · intro h; nlinarith
    · intro h; nlinarith
  unfold rsProfit kk
  rw [hy]
  by_cases h : y < p1 / qj
  · rw [if_pos (hc.mpr h), if_pos h]; ring
  · rw [if_neg (fun h' => h (hc.mp h')), if_neg h]; ring

lemma rsOpt_eq (P : Params) (hP : P.Standing) (qi qj p1 : ℝ) (hqi : 0 < qi) (hqj : 0 < qj)
    (hp0 : 0 ≤ p1) (hp1 : p1 < qj) :
    rsOpt P qi qj p1 = qi * rho P.α (p1 / qj) := by
  obtain ⟨_, _, ha0, ha1, _⟩ := hP
  have hr0 : 0 ≤ p1 / qj := div_nonneg hp0 hqj.le
  have hr1 : p1 / qj < 1 := by rw [div_lt_one hqj]; exact hp1
  have hG : IsGreatest (rsProfit P qi qj p1 '' Set.Ioc (0 : ℝ) qi) (qi * rho P.α (p1 / qj)) := by
    obtain ⟨hy0, hy1⟩ := ys_mem P.α (p1 / qj) ha0 ha1 hr0 hr1
    constructor
    · refine ⟨qi * ys P.α (p1 / qj), ⟨by positivity, ?_⟩, ?_⟩
      · nlinarith
      · rw [rsProfit_eq P qi qj p1 _ hqi hqj, kk_ys _ _ ha0 ha1 hr0 hr1]
    · rintro v ⟨p2, ⟨hp2a, hp2b⟩, rfl⟩
      have : p2 = qi * (p2 / qi) := by field_simp
      rw [this, rsProfit_eq P qi qj p1 _ hqi hqj]
      apply mul_le_mul_of_nonneg_left _ hqi.le
      exact kk_le _ _ _ ha0 ha1 hr0 hr1 (div_pos hp2a hqi) (by rw [div_le_one hqi]; exact hp2b)
  unfold rsOpt
  exact hG.csSup_eq

lemma profit_eq (P : Params) (hP : P.Standing) (qi qj p : ℝ) (hqi : 0 < qi) (hqj : 0 < qj)
    (hp0 : 0 ≤ p) (hp1 : p < qj) :
    profit P qi qj p = p * (1 - p / qj) + qi * phi P.α (p / qj) := by
  have hs : 0 ≤ 1 - p / qj := by
    have : p / qj < 1 := by rw [div_lt_one hqj]; exact hp1
    linarith
  unfold profit succ
  rw [max_eq_right hs, rsOpt_eq P hP qi qj p hqi hqj hp0 hp1]
  unfold phi; ring

lemma profit_zero (P : Params) (qi qj p : ℝ) (hqj : 0 < qj) (hp : qj ≤ p) :
    profit P qi qj p = 0 := by
  unfold profit succ
  have : 1 - p / qj ≤ 0 := by
    have : 1 ≤ p / qj := by rw [le_div_iff₀ hqj]; linarith
    linarith
  rw [max_eq_left this]; ring


lemma profit_eq2 (P : Params) (hP : P.Standing) (qi qj p : ℝ) (hqi : 0 < qi) (hqj : 0 < qj)
    (hp0 : 0 ≤ p) (hp1 : p < qj) :
    profit P qi qj p = qj * (p / qj) * (1 - p / qj) + qi * phi P.α (p / qj) := by
  rw [profit_eq P hP qi qj p hqi hqj hp0 hp1]
  have : qj * (p / qj) = p := by field_simp
  rw [this]

noncomputable def pL (P : Params) : ℝ := (3 + P.α) / 8 * P.qL
noncomputable def piL (P : Params) : ℝ := P.qL * (1 / 4 + ((3 + P.α) / 8) ^ 2)

lemma LL_pL (P : Params) (hP : P.Standing) : profit P P.qL P.qL (pL P) = piL P := by
  have hP' := hP
  obtain ⟨hl, hlh, ha0, ha1, _⟩ := hP'
  have hlt : pL P < P.qL := by unfold pL; nlinarith
  rw [profit_eq2 P hP _ _ _ hl hl (by unfold pL; positivity) hlt]
  have hs : pL P / P.qL = (3 + P.α) / 8 := by unfold pL; field_simp
  rw [hs, phi_case1 _ _ (by linarith)]
  unfold piL; ring

lemma LL_lt (P : Params) (hP : P.Standing) (x : ℝ) (hx0 : 0 ≤ x) (hne : x ≠ pL P) :
    profit P P.qL P.qL x < piL P := by
  have hP' := hP
  obtain ⟨hl, hlh, ha0, ha1, _⟩ := hP'
  have hpos : 0 < piL P := by unfold piL; positivity
  by_cases hxl : P.qL ≤ x
  · rw [profit_zero P _ _ _ hl hxl]; exact hpos
  push_neg at hxl
  rw [profit_eq2 P hP _ _ _ hl hl hx0 hxl]
  set s := x / P.qL with hs
  have hs0 : 0 ≤ s := div_nonneg hx0 hl.le
  have hs1 : s < 1 := by rw [hs, div_lt_one hl]; exact hxl
  unfold piL
  by_cases h2 : s ≤ 1 / 2
  · rw [phi_case1 _ _ h2]
    have hsne : s - (3 + P.α) / 8 ≠ 0 := by
      intro h; apply hne; unfold pL
      have : s = (3 + P.α) / 8 := by linarith
      rw [← this, hs]; field_simp
    have := mul_pos hl (pow_pos (abs_pos.mpr hsne) 2)
    rw [sq_abs] at this
    nlinarith
  · push_neg at h2
    have hph := phi_strict P.α (1/2) s ha0 ha1 (by norm_num) h2 hs1
    rw [phi_case1 _ _ (le_refl _)] at hph
    have : s * (1 - s) ≤ 1 / 4 := by nlinarith [sq_nonneg (s - 1/2)]
    have h3 : P.qL * s * (1 - s) ≤ P.qL * (1/4) := by
      rw [mul_assoc]; exact mul_le_mul_of_nonneg_left this hl.le
    have h4 : P.qL * phi P.α s < P.qL * ((1 - (1 - P.α) * (1 / 2)) / 4) :=
      mul_lt_mul_of_pos_left hph hl
    have h5 : (1 - (1 - P.α) * (1 / 2)) / 4 ≤ ((3 + P.α) / 8) ^ 2 + 0 := by
      nlinarith [sq_nonneg (1 - P.α)]
    nlinarith

lemma D_nonneg (P : Params) (hP : P.Standing) :
    0 ≤ (P.qH - P.qL) * (16 * P.qH - (1 - P.α) ^ 2 * P.qL) := by
  obtain ⟨hl, hlh, ha0, ha1, _⟩ := hP
  have : (1 - P.α) ^ 2 < 1 := by nlinarith
  have : (1 - P.α) ^ 2 * P.qL < 16 * P.qH := by nlinarith
  apply mul_nonneg <;> linarith

lemma pbar_eq (P : Params) : pbar P = (4 * P.qH - (1 - P.α) * P.qL -
    Real.sqrt ((P.qH - P.qL) * (16 * P.qH - (1 - P.α) ^ 2 * P.qL))) / 8 := rfl

lemma Q_ident (P : Params) (hP : P.Standing) (p : ℝ) :
    64 * (p - pbar P) * (p - (4 * P.qH - (1 - P.α) * P.qL +
      Real.sqrt ((P.qH - P.qL) * (16 * P.qH - (1 - P.α) ^ 2 * P.qL))) / 8) =
    64 * p ^ 2 - (64 * P.qH - 16 * (1 - P.α) * P.qL) * p + P.qH * P.qL * (3 + P.α) ^ 2 := by
  have hsq := Real.sq_sqrt (D_nonneg P hP)
  rw [pbar_eq]
  linear_combination (-1 : ℝ) * hsq

lemma LH_formula (P : Params) (hP : P.Standing) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ P.qH / 2) :
    64 * P.qH * (profit P P.qL P.qH p - piL P) =
      -(64 * p ^ 2 - (64 * P.qH - 16 * (1 - P.α) * P.qL) * p + P.qH * P.qL * (3 + P.α) ^ 2) := by
  have hP' := hP
  obtain ⟨hl, hlh, ha0, ha1, _⟩ := hP'
  have hh : 0 < P.qH := by linarith
  rw [profit_eq2 P hP _ _ _ hl hh hp0 (by linarith)]
  have hs : p / P.qH ≤ 1 / 2 := by rw [div_le_iff₀ hh]; linarith
  rw [phi_case1 _ _ hs]
  have hp : p = P.qH * (p / P.qH) := by field_simp
  set s := p / P.qH
  rw [hp]; unfold piL; ring

lemma sqrt_gt (P : Params) (hP : P.Standing) :
    4 * (P.qH - P.qL) < Real.sqrt ((P.qH - P.qL) * (16 * P.qH - (1 - P.α) ^ 2 * P.qL)) := by
  have hsq := Real.sq_sqrt (D_nonneg P hP)
  have hs0 := Real.sqrt_nonneg ((P.qH - P.qL) * (16 * P.qH - (1 - P.α) ^ 2 * P.qL))
  obtain ⟨hl, hlh, ha0, ha1, _⟩ := hP
  set S := Real.sqrt ((P.qH - P.qL) * (16 * P.qH - (1 - P.α) ^ 2 * P.qL))
  by_contra hc
  push_neg at hc
  have h1 : S ^ 2 ≤ (4 * (P.qH - P.qL)) ^ 2 := by
    apply pow_le_pow_left₀ hs0 hc
  have h2 : (1 - P.α) ^ 2 < 16 := by nlinarith
  have h3 : 0 < (P.qH - P.qL) * P.qL * (16 - (1 - P.α) ^ 2) := by
    apply mul_pos (mul_pos (by linarith) hl); linarith
  nlinarith

lemma pbar_lt_pL (P : Params) (hP : P.Standing) : pbar P < pL P := by
  have := sqrt_gt P hP
  rw [pbar_eq]; unfold pL
  linarith

lemma LH_gt (P : Params) (hP : P.Standing) (p : ℝ) (h1 : pbar P < p)
    (h2 : p ≤ (3 + P.α) / 8 * P.qH) (hp0 : 0 ≤ p) : piL P < profit P P.qL P.qH p := by
  have hP' := hP
  obtain ⟨hl, hlh, ha0, ha1, _⟩ := hP'
  have hh : 0 < P.qH := by linarith
  have hF := LH_formula P hP p hp0 (by nlinarith)
  have hQ := Q_ident P hP p
  have hs0 := Real.sqrt_nonneg ((P.qH - P.qL) * (16 * P.qH - (1 - P.α) ^ 2 * P.qL))
  set S := Real.sqrt ((P.qH - P.qL) * (16 * P.qH - (1 - P.α) ^ 2 * P.qL))
  have hlt2 : p < (4 * P.qH - (1 - P.α) * P.qL + S) / 8 := by nlinarith
  have hneg : 64 * (p - pbar P) * (p - (4 * P.qH - (1 - P.α) * P.qL + S) / 8) < 0 := by
    have : 0 < 64 * (p - pbar P) := by linarith
    exact mul_neg_of_pos_of_neg this (by linarith)
  have : 0 < 64 * P.qH * (profit P P.qL P.qH p - piL P) := by linarith
  have := (pos_iff_pos_of_mul_pos this).mp (by positivity)
  linarith

lemma LH_lt (P : Params) (hP : P.Standing) (p : ℝ) (hp0 : 0 ≤ p) (h1 : p < pbar P) :
    profit P P.qL P.qH p < piL P := by
  have hP' := hP
  obtain ⟨hl, hlh, ha0, ha1, _⟩ := hP'
  have hh : 0 < P.qH := by linarith
  have hpb := pbar_lt_pL P hP
  have hF := LH_formula P hP p hp0 (by unfold pL at hpb; nlinarith)
  have hQ := Q_ident P hP p
  have hs0 := Real.sqrt_nonneg ((P.qH - P.qL) * (16 * P.qH - (1 - P.α) ^ 2 * P.qL))
  set S := Real.sqrt ((P.qH - P.qL) * (16 * P.qH - (1 - P.α) ^ 2 * P.qL))
  have hlt2 : p < (4 * P.qH - (1 - P.α) * P.qL + S) / 8 := by
    rw [pbar_eq] at h1; linarith
  have hpos : 0 < 64 * (p - pbar P) * (p - (4 * P.qH - (1 - P.α) * P.qL + S) / 8) := by
    have : 64 * (p - pbar P) < 0 := by linarith
    exact mul_pos_of_neg_of_neg this (by linarith)
  have : 64 * P.qH * (profit P P.qL P.qH p - piL P) < 0 := by linarith
  have h64 : 0 < 64 * P.qH := by positivity
  have : profit P P.qL P.qH p - piL P < 0 := by
    by_contra hc; push_neg at hc; nlinarith
  linarith

lemma LH_eq (P : Params) (hP : P.Standing) (hp0 : 0 ≤ pbar P) :
    profit P P.qL P.qH (pbar P) = piL P := by
  have hP' := hP
  obtain ⟨hl, hlh, ha0, ha1, _⟩ := hP'
  have hh : 0 < P.qH := by linarith
  have hpb := pbar_lt_pL P hP
  have hF := LH_formula P hP (pbar P) hp0 (by unfold pL at hpb; nlinarith)
  have hQ := Q_ident P hP (pbar P)
  simp only [sub_self, mul_zero, zero_mul] at hQ
  have : 64 * P.qH * (profit P P.qL P.qH (pbar P) - piL P) = 0 := by linarith
  have h64 : (64 * P.qH) ≠ 0 := by positivity
  have := (mul_eq_zero.mp this).resolve_left h64
  linarith


lemma HH_formula (P : Params) (hP : P.Standing) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ P.qH / 2) :
    profit P P.qH P.qH p = p - p ^ 2 / P.qH + P.qH / 4 - (1 - P.α) * p / 4 := by
  have hP' := hP
  obtain ⟨hl, hlh, ha0, ha1, _⟩ := hP'
  have hh : 0 < P.qH := by linarith
  rw [profit_eq P hP _ _ _ hh hh hp0 (by linarith)]
  have hs : p / P.qH ≤ 1 / 2 := by rw [div_le_iff₀ hh]; linarith
  rw [phi_case1 _ _ hs]
  field_simp; ring

lemma HH_incr (P : Params) (hP : P.Standing) (p1 p2 : ℝ) (h0 : 0 ≤ p1) (h12 : p1 < p2)
    (h2 : p2 ≤ (3 + P.α) / 8 * P.qH) : profit P P.qH P.qH p1 < profit P P.qH P.qH p2 := by
  have hP' := hP
  obtain ⟨hl, hlh, ha0, ha1, _⟩ := hP'
  have hh : 0 < P.qH := by linarith
  rw [HH_formula P hP p1 h0 (by nlinarith), HH_formula P hP p2 (by linarith) (by nlinarith)]
  have key : (p2 - p1 ^ 2 / P.qH + P.qH / 4 - (1 - P.α) * p2 / 4) -
      (p1 - p1 ^ 2 / P.qH + P.qH / 4 - (1 - P.α) * p1 / 4) - (p2 ^ 2 - p1 ^ 2) * 0 =
      (p2 - p1) * (1 - (1 - P.α) / 4) := by ring
  have : (p2 - p1 ^ 2 / P.qH + P.qH / 4 - (1 - P.α) * p2 / 4) -
      (p1 - p1 ^ 2 / P.qH + P.qH / 4 - (1 - P.α) * p1 / 4) = (p2 - p1) * (1 - (1 - P.α) / 4) := by
    ring
  have e : p2 ^ 2 / P.qH - p1 ^ 2 / P.qH = (p2 - p1) * ((p1 + p2) / P.qH) := by field_simp; ring
  have hq : (p1 + p2) / P.qH < (3 + P.α) / 4 := by
    rw [div_lt_iff₀ hh]; nlinarith
  have : 0 < (p2 - p1) * ((1 - (1 - P.α) / 4) - (p1 + p2) / P.qH) := by
    apply mul_pos (by linarith); linarith
  nlinarith

lemma diff_H (P : Params) (hP : P.Standing) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p < P.qH) :
    profit P P.qH P.qH p - profit P P.qL P.qH p = (P.qH - P.qL) * phi P.α (p / P.qH) := by
  have hP' := hP
  obtain ⟨hl, hlh, ha0, ha1, _⟩ := hP'
  have hh : 0 < P.qH := by linarith
  rw [profit_eq P hP _ _ _ hh hh hp0 hp1, profit_eq P hP _ _ _ hl hh hp0 hp1]; ring

lemma diff_L (P : Params) (hP : P.Standing) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p < P.qL) :
    profit P P.qH P.qL p - profit P P.qL P.qL p = (P.qH - P.qL) * phi P.α (p / P.qL) := by
  have hP' := hP
  obtain ⟨hl, hlh, ha0, ha1, _⟩ := hP'
  have hh : 0 < P.qH := by linarith
  rw [profit_eq P hP _ _ _ hh hl hp0 hp1, profit_eq P hP _ _ _ hl hl hp0 hp1]; ring

lemma sqrt_ineq (P : Params) (hP : P.Standing)
    (hc : (P.qH - P.qL) * (1 - P.α) < (3 + P.α) * P.qL) :
    16 * P.qL * pbar P < P.qH * ((7 + P.α) * P.qL - (1 - P.α) * P.qH) := by
  have hsq := Real.sq_sqrt (D_nonneg P hP)
  have hs0 := Real.sqrt_nonneg ((P.qH - P.qL) * (16 * P.qH - (1 - P.α) ^ 2 * P.qL))
  rw [pbar_eq]
  obtain ⟨hl, hlh, ha0, ha1, _⟩ := hP
  set S := Real.sqrt ((P.qH - P.qL) * (16 * P.qH - (1 - P.α) ^ 2 * P.qL))
  set b := 1 - P.α with hb
  set l := P.qL
  set h := P.qH
  have hb0 : 0 < b := by rw [hb]; linarith
  have hbh : b * h < 4 * l := by
    have : (3 + P.α) = 4 - b := by rw [hb]; ring
    rw [this] at hc; nlinarith
  have hR : 0 < b * (h - l) * (h + 2 * l) := by
    apply mul_pos (mul_pos hb0 (by linarith)); linarith
  suffices hS : b * (h - l) * (h + 2 * l) < 2 * l * S by
    have : (7 + P.α) = 8 - b := by rw [hb]; ring
    rw [this]; nlinarith
  by_contra hcon
  push_neg at hcon
  have h1 : (2 * l * S) ^ 2 ≤ (b * (h - l) * (h + 2 * l)) ^ 2 :=
    pow_le_pow_left₀ (by positivity) hcon 2
  have h2 : (2 * l * S) ^ 2 = 4 * l ^ 2 * ((h - l) * (16 * h - b ^ 2 * l)) := by
    rw [mul_pow, hsq]; ring
  -- polynomial contradiction
  have hW : 0 < 4 * l ^ 3 + (h - l) * (h + 2 * l) ^ 2 := by
    have : 0 < (h - l) * (h + 2 * l) ^ 2 := by
      apply mul_pos (by linarith); exact pow_pos (by linarith) 2
    have : 0 < 4 * l ^ 3 := by positivity
    linarith
  have hb2 : b ^ 2 * h ^ 2 < 16 * l ^ 2 := by
    have : 0 ≤ b * h := mul_nonneg hb0.le (by linarith)
    nlinarith
  have h3 : b ^ 2 * h ^ 2 * (4 * l ^ 3 + (h - l) * (h + 2 * l) ^ 2) <
      16 * l ^ 2 * (4 * l ^ 3 + (h - l) * (h + 2 * l) ^ 2) := mul_lt_mul_of_pos_right hb2 hW
  have h4 : h ^ 2 * (4 * l ^ 2 * (16 * h - b ^ 2 * l) - b ^ 2 * (h - l) * (h + 2 * l) ^ 2) > 0 := by
    nlinarith [mul_pos (mul_pos (pow_pos hl 2) (pow_pos (by linarith : (0:ℝ) < h) 2))
      (by linarith : (0:ℝ) < h - l)]
  have h5 : 0 < 4 * l ^ 2 * (16 * h - b ^ 2 * l) - b ^ 2 * (h - l) * (h + 2 * l) ^ 2 := by
    by_contra hh; push_neg at hh
    have : h ^ 2 * (4 * l ^ 2 * (16 * h - b ^ 2 * l) - b ^ 2 * (h - l) * (h + 2 * l) ^ 2) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by positivity) hh
    linarith
  have h6 : (b * (h - l) * (h + 2 * l)) ^ 2 =
      (h - l) * (b ^ 2 * (h - l) * (h + 2 * l) ^ 2) := by ring
  have h7 : 0 < (h - l) * (4 * l ^ 2 * (16 * h - b ^ 2 * l) - b ^ 2 * (h - l) * (h + 2 * l) ^ 2) :=
    mul_pos (by linarith) h5
  nlinarith


set_option maxHeartbeats 1000000 in
lemma I1 (P : Params) (hP : P.Standing) (hT : P.T ≤ pbar P) (x : ℝ) (hx : P.T ≤ x) :
    profit P P.qH P.qL x < profit P P.qH P.qH (pbar P) := by
  have hP' := hP
  obtain ⟨hl, hlh, ha0, ha1, hT0⟩ := hP'
  have hh : 0 < P.qH := by linarith
  have hpb0 : 0 < pbar P := by linarith
  have hpbL := pbar_lt_pL P hP
  unfold pL at hpbL
  have hpbh : pbar P < P.qH / 2 := by nlinarith
  set t := pbar P / P.qH with ht
  have ht0 : 0 < t := div_pos hpb0 hh
  have ht1 : t < 1 / 2 := by rw [ht, div_lt_iff₀ hh]; linarith
  have hHH : profit P P.qH P.qH (pbar P) = piL P + (P.qH - P.qL) * phi P.α t := by
    have := diff_H P hP (pbar P) hpb0.le (by linarith)
    rw [LH_eq P hP hpb0.le] at this; linarith
  have hphit : phi P.α (1 / 2) < phi P.α t := phi_strict _ _ _ ha0 ha1 ht0.le ht1 (by norm_num)
  have hphit0 : 0 < phi P.α (1 / 2) := phi_pos _ _ ha0 ha1 (by norm_num) (by norm_num)
  have hpiL : 0 < piL P := by unfold piL; positivity
  have hhl : 0 < P.qH - P.qL := by linarith
  by_cases hxl : P.qL ≤ x
  · rw [profit_zero P _ _ _ hl hxl, hHH]
    have : 0 < (P.qH - P.qL) * phi P.α t := mul_pos hhl (by linarith)
    linarith
  push_neg at hxl
  have hx0 : 0 ≤ x := by linarith
  set s := x / P.qL with hs
  have hs0 : 0 < s := div_pos (by linarith) hl
  have hs1 : s < 1 := by rw [hs, div_lt_one hl]; exact hxl
  by_cases hs2 : 1 / 2 ≤ s
  · have hdl := diff_L P hP x hx0 hxl
    rw [← hs] at hdl
    have hLL : profit P P.qL P.qL x ≤ piL P := by
      by_cases hxe : x = pL P
      · rw [hxe, LL_pL P hP]
      · exact (LL_lt P hP x hx0 hxe).le
    have hph : phi P.α s ≤ phi P.α (1 / 2) := phi_anti _ _ _ ha0 ha1 (by norm_num) hs2 hs1
    have : (P.qH - P.qL) * phi P.α s < (P.qH - P.qL) * phi P.α t :=
      mul_lt_mul_of_pos_left (by linarith) hhl
    rw [hHH]; linarith
  · push_neg at hs2
    -- explicit quadratic case
    have hHL := profit_eq2 P hP P.qH P.qL x hh hl hx0 hxl
    rw [← hs, phi_case1 _ _ hs2.le] at hHL
    have hHH2 := profit_eq2 P hP P.qH P.qH (pbar P) hh hh hpb0.le (by linarith)
    rw [← ht, phi_case1 _ _ ht1.le] at hHH2
    have hE := profit_eq2 P hP P.qL P.qH (pbar P) hl hh hpb0.le (by linarith)
    rw [← ht, phi_case1 _ _ ht1.le, LH_eq P hP hpb0.le] at hE
    unfold piL at hE
    rw [hHL, hHH2]
    set l := P.qL
    set h := P.qH
    set a := P.α
    have hG : (h * t * (1 - t) + h * ((1 - (1 - a) * t) / 4)) -
        (l * s * (1 - s) + h * ((1 - (1 - a) * s) / 4)) =
        l * (s - (3 + a) / 8) ^ 2 + (h - l) * (1 - a) * (s - t) / 4 := by
      linear_combination (-1 : ℝ) * hE
    by_cases hc : (3 + a) * l ≤ (h - l) * (1 - a)
    · have hA : l * ((3 + a) / 8) ^ 2 - (h - l) * (1 - a) * t / 4 =
          h * t * (1 - t - (1 - a) / 4) := by linear_combination hE
      have hA2 : 0 < h * t * (1 - t - (1 - a) / 4) := by
        apply mul_pos (mul_pos hh ht0); linarith
      have hB : 0 ≤ s * (l * s - 2 * l * ((3 + a) / 8) + (h - l) * (1 - a) / 4) := by
        apply mul_nonneg hs0.le; nlinarith
      nlinarith [hG, hA, hA2, hB, sq_nonneg (s - (3 + a) / 8)]
    · push_neg at hc
      have hsq := sqrt_ineq P hP hc
      rw [show pbar P = h * t by rw [ht]; field_simp] at hsq
      have hsq2 : 16 * l * t < (7 + a) * l - (1 - a) * h := by
        have : h * (16 * l * t) < h * ((7 + a) * l - (1 - a) * h) := by linarith
        exact lt_of_mul_lt_mul_left this hh.le
      set κ := (h - l) * (1 - a) / 4 with hκ
      have hκ0 : 0 < κ := by rw [hκ]; apply div_pos (mul_pos hhl (by linarith)); norm_num
      have hk : κ < 4 * l * ((3 + a) / 8 - t) := by rw [hκ]; linarith
      have hsplit : 4 * l * (l * (s - (3 + a) / 8) ^ 2 + κ * (s - t)) =
          (2 * l * (s - (3 + a) / 8) + κ) ^ 2 + κ * (4 * l * ((3 + a) / 8 - t) - κ) := by ring
      have hpk : 0 < κ * (4 * l * ((3 + a) / 8 - t) - κ) := mul_pos hκ0 (by linarith only [hk])
      have h4 : 0 < 4 * l * (l * (s - (3 + a) / 8) ^ 2 + κ * (s - t)) := by
        have := sq_nonneg (2 * l * (s - (3 + a) / 8) + κ)
        linarith only [hsplit, this, hpk]
      have h5 : 0 < l * (s - (3 + a) / 8) ^ 2 + κ * (s - t) := by
        by_contra hh5; push_neg at hh5
        have : 4 * l * (l * (s - (3 + a) / 8) ^ 2 + κ * (s - t)) ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos (by linarith only [hl]) hh5
        linarith only [this, h4]
      have hκe : (h - l) * (1 - a) * (s - t) / 4 = κ * (s - t) := by rw [hκ]; ring
      linarith only [hG, h5, hκe]


lemma pL_lt (P : Params) (hP : P.Standing) : pL P < P.qL / 2 := by
  obtain ⟨hl, hlh, ha0, ha1, _⟩ := hP
  unfold pL; nlinarith

lemma LL_le (P : Params) (hP : P.Standing) (y : ℝ) (hy : 0 ≤ y) :
    profit P P.qL P.qL y ≤ piL P := by
  by_cases h : y = pL P
  · rw [h, LL_pL P hP]
  · exact (LL_lt P hP y hy h).le

lemma HL_pos (P : Params) (hP : P.Standing) (x : ℝ) (hx0 : 0 ≤ x) (hx : x < P.qL) :
    0 < profit P P.qH P.qL x := by
  have hP' := hP
  obtain ⟨hl, hlh, ha0, ha1, _⟩ := hP'
  rw [profit_eq P hP _ _ _ (by linarith) hl hx0 hx]
  have h1 : 0 ≤ 1 - x / P.qL := by
    have : x / P.qL < 1 := by rw [div_lt_one hl]; exact hx
    linarith
  have h2 := phi_pos P.α (x / P.qL) ha0 ha1 (div_nonneg hx0 hl.le) (by rw [div_lt_one hl]; exact hx)
  have : 0 < P.qH * phi P.α (x / P.qL) := mul_pos (by linarith) h2
  nlinarith [mul_nonneg hx0 h1]

lemma diff_trick (P : Params) (hP : P.Standing) (pH x : ℝ) (hpH0 : 0 ≤ pH) (hx0 : 0 ≤ x)
    (hxl : x < P.qL) (h1 : profit P P.qH P.qL x ≤ profit P P.qH P.qH pH)
    (h2 : profit P P.qL P.qH pH ≤ profit P P.qL P.qL x) :
    pH / P.qH ≤ x / P.qL ∧ pH < P.qH := by
  have hP' := hP
  obtain ⟨hl, hlh, ha0, ha1, _⟩ := hP'
  have hh : 0 < P.qH := by linarith
  have hpos := HL_pos P hP x hx0 hxl
  have hpH : pH < P.qH := by
    by_contra hc; push_neg at hc
    rw [profit_zero P _ _ _ hh hc] at h1; linarith
  refine ⟨?_, hpH⟩
  have d1 := diff_H P hP pH hpH0 hpH
  have d2 := diff_L P hP x hx0 hxl
  have hge : (P.qH - P.qL) * phi P.α (x / P.qL) ≤ (P.qH - P.qL) * phi P.α (pH / P.qH) := by
    linarith
  have hph : phi P.α (x / P.qL) ≤ phi P.α (pH / P.qH) :=
    le_of_mul_le_mul_left hge (by linarith)
  by_contra hc; push_neg at hc
  have := phi_strict P.α (x / P.qL) (pH / P.qH) ha0 ha1 (div_nonneg hx0 hl.le) hc
    (by rw [div_lt_one hh]; exact hpH)
  linarith

lemma LL_lt_LH (P : Params) (hP : P.Standing) (p : ℝ) (hp0 : 0 < p) (hp : p < P.qL) :
    profit P P.qL P.qL p < profit P P.qL P.qH p := by
  have hP' := hP
  obtain ⟨hl, hlh, ha0, ha1, _⟩ := hP'
  have hh : 0 < P.qH := by linarith
  rw [profit_eq P hP _ _ _ hl hl hp0.le hp, profit_eq P hP _ _ _ hl hh hp0.le (by linarith)]
  have hr : p / P.qH < p / P.qL := div_lt_div_of_pos_left hp0 hl hlh
  have hph := phi_anti P.α (p / P.qH) (p / P.qL) ha0 ha1 (div_nonneg hp0.le hh.le) hr.le
    (by rw [div_lt_one hl]; exact hp)
  have : p * (1 - p / P.qL) < p * (1 - p / P.qH) := mul_lt_mul_of_pos_left (by linarith) hp0
  nlinarith

lemma LL_sdec (P : Params) (hP : P.Standing) (y1 y2 : ℝ) (h1 : pL P ≤ y1) (h12 : y1 < y2)
    (hy1 : y1 < P.qL) : profit P P.qL P.qL y2 < profit P P.qL P.qL y1 := by
  have hP' := hP
  obtain ⟨hl, hlh, ha0, ha1, _⟩ := hP'
  have hpL0 : 0 < pL P := by unfold pL; positivity
  have hpos : 0 < profit P P.qL P.qL y1 := by
    have := LL_lt_LH P hP y1 (by linarith) hy1
    rw [profit_eq P hP _ _ _ hl hl (by linarith) hy1]
    have h2 := phi_pos P.α (y1 / P.qL) ha0 ha1 (div_nonneg (by linarith) hl.le)
      (by rw [div_lt_one hl]; exact hy1)
    have : 0 ≤ 1 - y1 / P.qL := by
      have : y1 / P.qL < 1 := by rw [div_lt_one hl]; exact hy1
      linarith
    nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ y1) this, mul_pos hl h2]
  by_cases hy2 : P.qL ≤ y2
  · rw [profit_zero P _ _ _ hl hy2]; exact hpos
  push_neg at hy2
  rw [profit_eq2 P hP _ _ _ hl hl (by linarith) hy1, profit_eq2 P hP _ _ _ hl hl (by linarith) hy2]
  set s1 := y1 / P.qL with hs1
  set s2 := y2 / P.qL with hs2
  have hs12 : s1 < s2 := div_lt_div_of_pos_right h12 hl
  have hss : (3 + P.α) / 8 ≤ s1 := by
    rw [hs1, le_div_iff₀ hl]; unfold pL at h1; linarith
  have hs2l : s2 < 1 := by rw [hs2, div_lt_one hl]; exact hy2
  -- generic: quadratic part and phi part
  have hq : ∀ u v : ℝ, (3 + P.α) / 8 ≤ u → u < v → v ≤ 1 / 2 →
      P.qL * v * (1 - v) + P.qL * phi P.α v < P.qL * u * (1 - u) + P.qL * phi P.α u := by
    intro u v hu huv hv
    rw [phi_case1 _ _ hv, phi_case1 _ _ (by linarith)]
    have : 0 < (v - u) * (u + v - (3 + P.α) / 4) := mul_pos (by linarith) (by linarith)
    nlinarith [mul_pos hl this]
  have hr : ∀ u v : ℝ, 1 / 2 ≤ u → u < v → v < 1 →
      P.qL * v * (1 - v) + P.qL * phi P.α v < P.qL * u * (1 - u) + P.qL * phi P.α u := by
    intro u v hu huv hv
    have hp := phi_strict P.α u v ha0 ha1 (by linarith) huv hv
    have : v * (1 - v) ≤ u * (1 - u) := by nlinarith
    nlinarith [mul_lt_mul_of_pos_left hp hl, mul_le_mul_of_nonneg_left this hl.le]
  by_cases hA : s2 ≤ 1 / 2
  · exact hq s1 s2 hss hs12 hA
  push_neg at hA
  by_cases hB : 1 / 2 ≤ s1
  · exact hr s1 s2 hB hs12 hs2l
  push_neg at hB
  have e1 := hq s1 (1 / 2) hss hB (le_refl _)
  have e2 := hr (1 / 2) s2 (le_refl _) hA hs2l
  linarith



lemma gen_formula (P : Params) (hP : P.Standing) (qi qj p : ℝ) (hqi : 0 < qi) (hqj : 0 < qj)
    (hp0 : 0 ≤ p) (hp1 : p ≤ qj / 2) :
    profit P qi qj p = p - p ^ 2 / qj + qi / 4 - (1 - P.α) * qi * p / (4 * qj) := by
  rw [profit_eq P hP _ _ _ hqi hqj hp0 (by linarith)]
  have hs : p / qj ≤ 1 / 2 := by rw [div_le_iff₀ hqj]; linarith
  rw [phi_case1 _ _ hs]
  field_simp; ring

lemma gen_pos (P : Params) (hP : P.Standing) (qi qj p : ℝ) (hqi : 0 < qi) (hqj : 0 < qj)
    (hp0 : 0 ≤ p) (hp1 : p < qj) : 0 < profit P qi qj p := by
  have hP' := hP
  obtain ⟨_, _, ha0, ha1, _⟩ := hP'
  rw [profit_eq P hP _ _ _ hqi hqj hp0 hp1]
  have h1 : 0 ≤ 1 - p / qj := by
    have : p / qj < 1 := by rw [div_lt_one hqj]; exact hp1
    linarith
  have h2 := phi_pos P.α (p / qj) ha0 ha1 (div_nonneg hp0 hqj.le) (by rw [div_lt_one hqj]; exact hp1)
  nlinarith [mul_nonneg hp0 h1, mul_pos hqi h2]

lemma gen_incr (P : Params) (hP : P.Standing) (qi qj p1 p2 : ℝ) (hqi : 0 < qi) (hqj : 0 < qj)
    (h0 : 0 ≤ p1) (h12 : p1 < p2) (h2 : p2 ≤ (4 * qj - (1 - P.α) * qi) / 8) :
    profit P qi qj p1 < profit P qi qj p2 := by
  have hP' := hP
  obtain ⟨_, _, ha0, ha1, _⟩ := hP'
  have hb : 0 < (1 - P.α) * qi := mul_pos (by linarith) hqi
  rw [gen_formula P hP _ _ _ hqi hqj h0 (by linarith), gen_formula P hP _ _ _ hqi hqj (by linarith) (by linarith)]
  have e : (p2 - p2 ^ 2 / qj + qi / 4 - (1 - P.α) * qi * p2 / (4 * qj)) -
      (p1 - p1 ^ 2 / qj + qi / 4 - (1 - P.α) * qi * p1 / (4 * qj)) =
      (p2 - p1) * (1 - (p1 + p2) / qj - (1 - P.α) * qi / (4 * qj)) := by field_simp; ring
  have : (p1 + p2) / qj + (1 - P.α) * qi / (4 * qj) < 1 := by
    rw [div_add_div _ _ hqj.ne' (by positivity), div_lt_one (by positivity)]; nlinarith
  have : 0 < (p2 - p1) * (1 - (p1 + p2) / qj - (1 - P.α) * qi / (4 * qj)) :=
    mul_pos (by linarith) (by linarith)
  linarith

lemma gen_decr (P : Params) (hP : P.Standing) (qi qj p1 p2 : ℝ) (hqi : 0 < qi) (hqj : 0 < qj)
    (h0 : 0 ≤ p1) (hv : (4 * qj - (1 - P.α) * qi) / 8 ≤ p1) (h12 : p1 < p2) (h1 : p1 < qj) :
    profit P qi qj p2 < profit P qi qj p1 := by
  have hP' := hP
  obtain ⟨_, _, ha0, ha1, _⟩ := hP'
  have hpos := gen_pos P hP qi qj p1 hqi hqj h0 h1
  by_cases hp2 : qj ≤ p2
  · rw [profit_zero P _ _ _ hqj hp2]; exact hpos
  push_neg at hp2
  have hb : 0 < (1 - P.α) * qi := mul_pos (by linarith) hqi
  have hq : ∀ u v : ℝ, (4 * qj - (1 - P.α) * qi) / 8 ≤ u → 0 ≤ u → u < v → v ≤ qj / 2 →
      profit P qi qj v < profit P qi qj u := by
    intro u v hu hu0 huv hv
    rw [gen_formula P hP _ _ _ hqi hqj hu0 (by linarith), gen_formula P hP _ _ _ hqi hqj (by linarith) hv]
    have e : (u - u ^ 2 / qj + qi / 4 - (1 - P.α) * qi * u / (4 * qj)) -
        (v - v ^ 2 / qj + qi / 4 - (1 - P.α) * qi * v / (4 * qj)) =
        (v - u) * ((u + v) / qj + (1 - P.α) * qi / (4 * qj) - 1) := by field_simp; ring
    have : 1 < (u + v) / qj + (1 - P.α) * qi / (4 * qj) := by
      rw [div_add_div _ _ hqj.ne' (by positivity), one_lt_div (by positivity)]; nlinarith
    have : 0 < (v - u) * ((u + v) / qj + (1 - P.α) * qi / (4 * qj) - 1) :=
      mul_pos (by linarith) (by linarith)
    linarith
  have hr : ∀ u v : ℝ, qj / 2 ≤ u → u < v → v < qj →
      profit P qi qj v < profit P qi qj u := by
    intro u v hu huv hv
    rw [profit_eq P hP qi qj u hqi hqj (by linarith) (by linarith),
      profit_eq P hP qi qj v hqi hqj (by linarith) hv]
    have hp := phi_anti P.α (u / qj) (v / qj) ha0 ha1 (div_nonneg (by linarith) hqj.le)
      (div_le_div_of_nonneg_right huv.le hqj.le) (by rw [div_lt_one hqj]; exact hv)
    have e : u * (1 - u / qj) - v * (1 - v / qj) = (v - u) * ((u + v) / qj - 1) := by
      field_simp; ring
    have : 1 < (u + v) / qj := by rw [one_lt_div hqj]; linarith
    have : 0 < (v - u) * ((u + v) / qj - 1) := mul_pos (by linarith) (by linarith)
    nlinarith [mul_le_mul_of_nonneg_left hp hqi.le]
  by_cases hA : p2 ≤ qj / 2
  · exact hq p1 p2 hv h0 h12 hA
  push_neg at hA
  by_cases hB : qj / 2 ≤ p1
  · exact hr p1 p2 hB h12 hp2
  push_neg at hB
  have e1 := hq p1 (qj / 2) hv h0 hB le_rfl
  have e2 := hr (qj / 2) p2 le_rfl hA hp2
  linarith

lemma gen_greatest (P : Params) (hP : P.Standing) (qi qj : ℝ) (hqi : 0 < qi) (hqj : 0 < qj)
    (hT : P.T < qj) :
    IsGreatest (profit P qi qj '' Set.Ici P.T)
      (profit P qi qj (max ((4 * qj - (1 - P.α) * qi) / 8) P.T)) := by
  have hP' := hP
  obtain ⟨_, _, ha0, ha1, hT0⟩ := hP'
  set v := (4 * qj - (1 - P.α) * qi) / 8
  have hvq : v < qj := by
    have : 0 < (1 - P.α) * qi := mul_pos (by linarith) hqi
    simp only [v]; linarith
  have hm : max v P.T < qj := max_lt hvq hT
  refine ⟨⟨max v P.T, show P.T ≤ max v P.T from le_max_right _ _, rfl⟩, ?_⟩
  rintro y ⟨x, hx, rfl⟩
  have hx : P.T ≤ x := hx
  rcases le_or_gt x (max v P.T) with h | h
  · rcases h.lt_or_eq with h' | h'
    · -- x < max v T, so max = v > T
      have hmv : max v P.T = v := by
        rcases le_total v P.T with hh | hh
        · rw [max_eq_right hh] at h'; linarith
        · exact max_eq_left hh
      rw [hmv] at h' ⊢
      exact (gen_incr P hP qi qj x v hqi hqj (by linarith) h' le_rfl).le
    · rw [h']
  · by_cases hxq : qj ≤ x
    · rw [profit_zero P _ _ _ hqj hxq]
      exact (gen_pos P hP qi qj _ hqi hqj (by linarith [le_max_right v P.T]) hm).le
    · push_neg at hxq
      exact (gen_decr P hP qi qj _ x hqi hqj (by linarith [le_max_right v P.T])
        (le_max_left _ _) h hm).le

lemma optProfit_eq (P : Params) (hP : P.Standing) (qi qj : ℝ) (hqi : 0 < qi) (hqj : 0 < qj)
    (hT : P.T < qj) :
    optProfit P qi qj = profit P qi qj (max ((4 * qj - (1 - P.α) * qi) / 8) P.T) := by
  unfold optProfit
  exact (gen_greatest P hP qi qj hqi hqj hT).csSup_eq

lemma isG (P : Params) (hP : P.Standing) (qi qj p1 : ℝ) (hqi : 0 < qi) (hqj : 0 < qj)
    (hp0 : 0 ≤ p1) (hp1 : p1 < qj) :
    IsGreatest (rsProfit P qi qj p1 '' Set.Ioc (0 : ℝ) qi) (qi * rho P.α (p1 / qj)) ∧
    qi * ys P.α (p1 / qj) ∈ Set.Ioc (0 : ℝ) qi ∧
    rsProfit P qi qj p1 (qi * ys P.α (p1 / qj)) = qi * rho P.α (p1 / qj) := by
  obtain ⟨_, _, ha0, ha1, _⟩ := hP
  have hr0 : 0 ≤ p1 / qj := div_nonneg hp0 hqj.le
  have hr1 : p1 / qj < 1 := by rw [div_lt_one hqj]; exact hp1
  obtain ⟨hy0, hy1⟩ := ys_mem P.α (p1 / qj) ha0 ha1 hr0 hr1
  have hmem : qi * ys P.α (p1 / qj) ∈ Set.Ioc (0 : ℝ) qi := ⟨by positivity, by nlinarith⟩
  have hval : rsProfit P qi qj p1 (qi * ys P.α (p1 / qj)) = qi * rho P.α (p1 / qj) := by
    rw [rsProfit_eq P qi qj p1 _ hqi hqj, kk_ys _ _ ha0 ha1 hr0 hr1]
  refine ⟨⟨⟨_, hmem, hval⟩, ?_⟩, hmem, hval⟩
  rintro v ⟨p2, ⟨hp2a, hp2b⟩, rfl⟩
  have : p2 = qi * (p2 / qi) := by field_simp
  rw [this, rsProfit_eq P qi qj p1 _ hqi hqj]
  apply mul_le_mul_of_nonneg_left _ hqi.le
  exact kk_le _ _ _ ha0 ha1 hr0 hr1 (div_pos hp2a hqi) (by rw [div_le_one hqi]; exact hp2b)


lemma LH_gt2 (P : Params) (hP : P.Standing) (p : ℝ) (h1 : pbar P < p)
    (h2 : p ≤ (4 * P.qH - (1 - P.α) * P.qL) / 8) (hp0 : 0 ≤ p) : piL P < profit P P.qL P.qH p := by
  have hP' := hP
  obtain ⟨hl, hlh, ha0, ha1, _⟩ := hP'
  have hh : 0 < P.qH := by linarith
  have hF := LH_formula P hP p hp0 (by nlinarith)
  have hQ := Q_ident P hP p
  have hsg := sqrt_gt P hP
  set S := Real.sqrt ((P.qH - P.qL) * (16 * P.qH - (1 - P.α) ^ 2 * P.qL))
  have hlt2 : p < (4 * P.qH - (1 - P.α) * P.qL + S) / 8 := by linarith
  have hneg : 64 * (p - pbar P) * (p - (4 * P.qH - (1 - P.α) * P.qL + S) / 8) < 0 := by
    have : 0 < 64 * (p - pbar P) := by linarith
    exact mul_neg_of_pos_of_neg this (by linarith)
  have : 0 < 64 * P.qH * (profit P P.qL P.qH p - piL P) := by linarith
  have := (pos_iff_pos_of_mul_pos this).mp (by positivity)
  linarith

end CSOP1Aux

open CrowdSignal.OnePrice CSOP1Aux in
theorem solution (P : Params) (hP : P.Standing) (hT : P.T ≤ pbar P) :
    optProfit P P.qH P.qL < profit P P.qH P.qH (pbar P) ∧
    (∀ pbar' punder' : ℝ,
      (3 + P.α) / 8 * P.qL < pbar' → pbar' ≤ P.qH →
      profit P P.qL P.qH pbar' = optProfit P P.qL P.qL →
      max ((4 * P.qL - (1 - P.α) * P.qH) / 8) P.T < punder' →
      punder' ≤ P.qH →
      profit P P.qH P.qH punder' = optProfit P P.qH P.qL →
      punder' < pbar') := by
  have hP' := hP
  obtain ⟨hl, hlh, ha0, ha1, hT0⟩ := hP'
  have hh : 0 < P.qH := by linarith
  have hpbL := pbar_lt_pL P hP
  have hpLl := pL_lt P hP
  have hpL0 : 0 < pL P := by unfold pL; positivity
  have hTl : P.T < P.qL := by linarith
  have hoptHL := optProfit_eq P hP P.qH P.qL hh hl hTl
  have hoptLL : optProfit P P.qL P.qL = piL P := by
    rw [optProfit_eq P hP P.qL P.qL hl hl hTl]
    have : (4 * P.qL - (1 - P.α) * P.qL) / 8 = pL P := by unfold pL; ring
    rw [this, max_eq_left (by linarith), LL_pL P hP]
  set x0 := max ((4 * P.qL - (1 - P.α) * P.qH) / 8) P.T with hx0
  have hx0T : P.T ≤ x0 := le_max_right _ _
  have hx0l : x0 < P.qL := by
    apply max_lt _ hTl
    have : 0 < (1 - P.α) * P.qH := mul_pos (by linarith) hh
    linarith
  refine ⟨?_, ?_⟩
  · rw [hoptHL]; exact I1 P hP hT x0 hx0T
  · intro pb' pu' h1 h2 h3 h4 h5 h6
    rw [hoptLL] at h3
    rw [hoptHL] at h6
    have hpLdef : (3 + P.α) / 8 * P.qL = pL P := rfl
    rw [hpLdef] at h1
    by_contra hc
    push_neg at hc
    have hv : (4 * P.qH - (1 - P.α) * P.qL) / 8 < pb' := by
      by_contra hc2; push_neg at hc2
      have := LH_gt2 P hP pb' (by linarith) hc2 (by linarith)
      linarith
    have hHLpos := HL_pos P hP x0 (by linarith) hx0l
    have hpuh : pu' < P.qH := by
      by_contra hc3; push_neg at hc3
      rw [profit_zero P _ _ _ hh hc3] at h6
      linarith
    have hLHle : profit P P.qL P.qH pu' ≤ piL P := by
      rcases hc.lt_or_eq with hlt | heq
      · have := gen_decr P hP P.qL P.qH pb' pu' hl hh (by linarith) hv.le hlt (by linarith)
        linarith
      · rw [← heq, h3]
    have hHLpL : profit P P.qH P.qL (pL P) ≤ profit P P.qH P.qH pu' := by
      rw [h6]
      exact (gen_greatest P hP P.qH P.qL hh hl hTl).2 ⟨pL P, show P.T ≤ pL P by linarith, rfl⟩
    rw [← LL_pL P hP] at hLHle
    obtain ⟨hdt, _⟩ := diff_trick P hP pu' (pL P) (by linarith) hpL0.le (by linarith) hHLpL hLHle
    have : pL P / P.qL = (3 + P.α) / 8 := by unfold pL; field_simp
    rw [this, div_le_iff₀ hh] at hdt
    have : (3 + P.α) / 8 * P.qH < (4 * P.qH - (1 - P.α) * P.qL) / 8 := by nlinarith
    linarith
