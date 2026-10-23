-- Prove2me | solution 1 for CrowdSignal.OnePrice.lemma_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-22T17:53:13.939711+00:00
-- url     : https://prove2.me/submissions/4092bd28-5d08-490b-8201-06acfc68e3a7

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

end CSOP1Aux

open CrowdSignal.OnePrice CSOP1Aux in
theorem solution (P : Params) (hP : P.Standing) (qi qj p1 : ℝ)
    (hi : qi = P.qL ∨ qi = P.qH) (hj : qj = P.qL ∨ qj = P.qH)
    (hfund : P.T ≤ p1) (hbelow : p1 < qj) :
    (p1 < qj / 2 →
      qi / 2 ∈ Set.Ioc (0 : ℝ) qi ∧
      IsGreatest (rsProfit P qi qj p1 '' Set.Ioc (0 : ℝ) qi)
        ((P.α / (1 - p1 / qj) + (1 - P.α)) * qi / 4) ∧
      rsProfit P qi qj p1 (qi / 2) =
        (P.α / (1 - p1 / qj) + (1 - P.α)) * qi / 4) ∧
    (qj / 2 ≤ p1 → p1 < min (qj / (2 * (1 - P.α))) qj →
      p1 * qi / qj ∈ Set.Ioc (0 : ℝ) qi ∧
      IsGreatest (rsProfit P qi qj p1 '' Set.Ioc (0 : ℝ) qi)
        (P.α * (p1 * qi / qj) +
          (1 - P.α) * (1 - p1 / qj) * (p1 * qi / qj)) ∧
      rsProfit P qi qj p1 (p1 * qi / qj) =
        P.α * (p1 * qi / qj) +
          (1 - P.α) * (1 - p1 / qj) * (p1 * qi / qj)) ∧
    (min (qj / (2 * (1 - P.α))) qj ≤ p1 →
      qi / (2 * (1 - P.α)) ∈ Set.Ioc (0 : ℝ) qi ∧
      IsGreatest (rsProfit P qi qj p1 '' Set.Ioc (0 : ℝ) qi)
        (P.α * (qi / (2 * (1 - P.α))) +
          (1 - 1 / (2 * (1 - P.α))) * qi / 2) ∧
      rsProfit P qi qj p1 (qi / (2 * (1 - P.α))) =
        P.α * (qi / (2 * (1 - P.α))) +
          (1 - 1 / (2 * (1 - P.α))) * qi / 2) := by
  have hP' := hP
  obtain ⟨hl, hlh, ha0, ha1, hT0⟩ := hP'
  have hqi : 0 < qi := by rcases hi with h | h <;> rw [h] <;> linarith
  have hqj : 0 < qj := by rcases hj with h | h <;> rw [h] <;> linarith
  have hp0 : 0 ≤ p1 := by linarith
  obtain ⟨hG, hmem, hval⟩ := isG P hP qi qj p1 hqi hqj hp0 hbelow
  set r := p1 / qj with hr
  have hb : 0 < 1 - P.α := by linarith
  have h1r : 0 < 1 - r := by
    have : r < 1 := by rw [hr, div_lt_one hqj]; exact hbelow
    linarith
  refine ⟨fun h1 => ?_, fun h1 h2 => ?_, fun h1 => ?_⟩
  · have hr2 : r ≤ 1 / 2 := by rw [hr, div_le_iff₀ hqj]; linarith
    have e1 : qi / 2 = qi * ys P.α r := by unfold ys; rw [if_pos hr2]; ring
    have e2 : (P.α / (1 - r) + (1 - P.α)) * qi / 4 = qi * rho P.α r := by
      unfold rho; rw [if_pos hr2]; ring
    rw [e2, e1]; exact ⟨hmem, hG, hval⟩
  · have hm : p1 < qj / (2 * (1 - P.α)) := lt_of_lt_of_le h2 (min_le_left _ _)
    have hr2 : 1 / 2 ≤ r := by rw [hr, le_div_iff₀ hqj]; linarith
    have hr3 : 2 * (1 - P.α) * r ≤ 1 := by
      rw [lt_div_iff₀ (by positivity)] at hm
      rw [hr]; rw [show 2 * (1 - P.α) * (p1 / qj) = (p1 * (2 * (1 - P.α))) / qj by ring,
        div_le_one hqj]; linarith
    have e1 : p1 * qi / qj = qi * ys P.α r := by
      unfold ys
      by_cases h : r ≤ 1 / 2
      · rw [if_pos h]
        have : r = 1 / 2 := le_antisymm h hr2
        rw [← this, hr]; ring
      · rw [if_neg h, if_pos hr3, hr]; ring
    have e2 : P.α * (p1 * qi / qj) + (1 - P.α) * (1 - r) * (p1 * qi / qj)
        = qi * rho P.α r := by
      have hp : p1 * qi / qj = qi * r := by rw [hr]; ring
      rw [hp]
      unfold rho
      by_cases h : r ≤ 1 / 2
      · rw [if_pos h]
        have : r = 1 / 2 := le_antisymm h hr2
        rw [this]; field_simp; ring
      · rw [if_neg h, if_pos hr3]; ring
    rw [e2, e1]; exact ⟨hmem, hG, hval⟩
  · have hm : qj / (2 * (1 - P.α)) ≤ p1 := by
      rcases min_le_iff.mp h1 with h | h
      · exact h
      · linarith
    have hr3 : 1 ≤ 2 * (1 - P.α) * r := by
      rw [div_le_iff₀ (by positivity)] at hm
      rw [hr, show 2 * (1 - P.α) * (p1 / qj) = (p1 * (2 * (1 - P.α))) / qj by ring,
        le_div_iff₀ hqj]; linarith
    have hr2 : ¬ r ≤ 1 / 2 := by
      intro h
      have : 2 * (1 - P.α) * r < 1 := by nlinarith
      linarith
    have e1 : qi / (2 * (1 - P.α)) = qi * ys P.α r := by
      unfold ys; rw [if_neg hr2]
      by_cases h : 2 * (1 - P.α) * r ≤ 1
      · rw [if_pos h]
        have : 2 * (1 - P.α) * r = 1 := le_antisymm h hr3
        field_simp; linarith
      · rw [if_neg h]; ring
    have e2 : P.α * (qi / (2 * (1 - P.α))) + (1 - 1 / (2 * (1 - P.α))) * qi / 2
        = qi * rho P.α r := by
      unfold rho; rw [if_neg hr2]
      by_cases h : 2 * (1 - P.α) * r ≤ 1
      · rw [if_pos h]
        have : 2 * (1 - P.α) * r = 1 := le_antisymm h hr3
        have hrr : r = 1 / (2 * (1 - P.α)) := by field_simp; linarith
        rw [hrr]; field_simp; ring
      · rw [if_neg h]; field_simp; ring
    rw [e2, e1]; exact ⟨hmem, hG, hval⟩
