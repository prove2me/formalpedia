-- Prove2me | solution 1 for BundleSearch.MatureNew.proposition_2_iii
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T17:48:31.976183+00:00
-- url     : https://prove2.me/submissions/9372fc45-7cd2-4f71-8ce2-79b9614559e0

import Mathlib
import Definitions.Def_BundleSearch_MatureNew_Model

set_option autoImplicit false
open BundleSearch.MatureNew MeasureTheory

lemma mn_meanVal : meanVal = 1 / 2 := by
  unfold meanVal
  rw [integral_id]; norm_num

lemma mn_probGe (t : ℝ) (h0 : 0 ≤ t) (h1 : t ≤ 1) : probGe t = 1 - t := by
  have : {v : ℝ | v ∈ Set.Icc (0:ℝ) 1 ∧ t ≤ v} = Set.Icc t 1 := by
    ext v
    simp only [Set.mem_setOf_eq, Set.mem_Icc]
    constructor
    · rintro ⟨⟨_, h⟩, h'⟩; exact ⟨h', h⟩
    · rintro ⟨h, h'⟩; exact ⟨⟨by linarith, h'⟩, h⟩
  unfold probGe
  rw [this, Real.volume_Icc, ENNReal.toReal_ofReal (by linarith)]

lemma mn_probGe_gt (t : ℝ) (h1 : 1 < t) : probGe t = 0 := by
  have : {v : ℝ | v ∈ Set.Icc (0:ℝ) 1 ∧ t ≤ v} = ∅ := by
    ext v
    simp only [Set.mem_setOf_eq, Set.mem_Icc, Set.mem_empty_iff_false, iff_false]
    rintro ⟨⟨_, h⟩, h'⟩; linarith
  unfold probGe
  rw [this]; simp

lemma mn_search (c p : ℝ) (h0 : 0 ≤ p) (h1 : p ≤ 1) :
    searchPayoffNew c p = (1 - p) ^ 2 / 2 - c := by
  unfold searchPayoffNew
  have hint : ∀ a b : ℝ, IntervalIntegrable (fun v : ℝ => max (v - p) 0) volume a b :=
    fun a b => (by fun_prop : Continuous fun v : ℝ => max (v - p) 0).intervalIntegrable a b
  rw [← intervalIntegral.integral_add_adjacent_intervals (hint 0 p) (hint p 1)]
  have e1 : ∫ v in (0:ℝ)..p, max (v - p) 0 = 0 := by
    rw [intervalIntegral.integral_congr (g := fun _ => (0:ℝ))]
    · simp
    · intro v hv
      rw [Set.uIcc_of_le h0] at hv
      exact max_eq_right (by linarith [hv.2])
  have e2 : ∫ v in p..1, max (v - p) 0 = (1 - p) ^ 2 / 2 := by
    rw [intervalIntegral.integral_congr (g := fun v => v - p)]
    · rw [intervalIntegral.integral_comp_sub_right (fun x : ℝ => x) p, integral_id]
      ring
    · intro v hv
      rw [Set.uIcc_of_le h1] at hv
      exact max_eq_left (by linarith [hv.1])
  rw [e1, e2]; ring

lemma mn_demand (c p : ℝ) (hp : 0 ≤ p) :
    demandNew c p = if (p ≤ 1 / 2 ∧ p ^ 2 ≤ 2 * c) then 1
      else if (p ≤ 1 ∧ 2 * c ≤ (1 - p) ^ 2) then 1 - p else 0 := by
  classical
  have hB : BuysWithoutSearch (nsPayoffNew p) (searchPayoffNew c p) ↔
      (p ≤ 1 / 2 ∧ p ^ 2 ≤ 2 * c) := by
    unfold BuysWithoutSearch nsPayoffNew
    rw [mn_meanVal]
    by_cases h1 : p ≤ 1
    · rw [mn_search c p hp h1]
      constructor
      · rintro ⟨a, b⟩; constructor <;> nlinarith
      · rintro ⟨a, b⟩; constructor <;> nlinarith
    · push_neg at h1
      constructor
      · rintro ⟨a, b⟩; linarith
      · rintro ⟨a, b⟩; linarith
  have hS : SearchesNew c p ↔
      (¬ (p ≤ 1 / 2 ∧ p ^ 2 ≤ 2 * c) ∧ (p ≤ 1 ∧ 2 * c ≤ (1 - p) ^ 2)) := by
    unfold SearchesNew Searches
    rw [hB]
    by_cases h1 : p ≤ 1
    · rw [mn_search c p hp h1]
      constructor
      · rintro ⟨⟨a, b⟩, d⟩; exact ⟨a, d, by nlinarith⟩
      · rintro ⟨a, d, e⟩; exact ⟨⟨a, by nlinarith⟩, d⟩
    · push_neg at h1
      constructor
      · rintro ⟨⟨a, b⟩, d⟩; exact absurd d (not_le.2 h1)
      · rintro ⟨a, d, e⟩; exact absurd d (not_le.2 h1)
  unfold demandNew
  by_cases h1 : p ≤ 1 / 2 ∧ p ^ 2 ≤ 2 * c
  · rw [if_pos (hB.2 h1), if_pos h1]
  · rw [if_neg (fun h => h1 (hB.1 h)), if_neg h1]
    by_cases h2 : p ≤ 1 ∧ 2 * c ≤ (1 - p) ^ 2
    · rw [if_pos (hS.2 ⟨h1, h2⟩), if_pos h2, mn_probGe p hp h2.1]
    · rw [if_neg (fun h => h2 (hS.1 h).2), if_neg h2]

lemma mn_search_neg (c a : ℝ) (h : a < 0) : searchPayoffNew c a = 1 / 2 - a - c := by
  unfold searchPayoffNew
  have : ∫ v in (0:ℝ)..1, max (v - a) 0 = ∫ v in (0:ℝ)..1, (v - a) := by
    apply intervalIntegral.integral_congr
    intro v hv
    rw [Set.uIcc_of_le (by norm_num)] at hv
    exact max_eq_left (by linarith [hv.1])
  rw [this, intervalIntegral.integral_sub (by simp) (by simp)]
  simp [integral_id]

lemma mn_buy (c p v1 : ℝ) : buyProbB c p v1 = demandNew c (p - v1) := by
  have h1 : nsPayoffB p v1 = nsPayoffNew (p - v1) := by
    unfold nsPayoffB nsPayoffNew; ring
  have h2 : searchPayoffB c p v1 = searchPayoffNew c (p - v1) := by
    unfold searchPayoffB searchPayoffNew
    congr 1
    apply intervalIntegral.integral_congr
    intro v _
    simp only
    congr 1; ring
  unfold buyProbB demandNew SearchesB SearchesNew
  rw [h1, h2]

noncomputable def mnDA (q a : ℝ) : ℝ := if a ≤ q then 1 else if a ≤ 1 - q then 1 - a else 0
noncomputable def mnDB (a : ℝ) : ℝ := if a ≤ 1 / 2 then 1 else 0

lemma mn_demand_all (c a : ℝ) :
    0 ≤ c → c ≤ 1 / 8 → demandNew c a = mnDA (Real.sqrt (2 * c)) a := by
  intro hc hc'
  have hq0 : 0 ≤ Real.sqrt (2 * c) := Real.sqrt_nonneg _
  have hq2 : Real.sqrt (2 * c) ^ 2 = 2 * c := Real.sq_sqrt (by linarith)
  have hq1 : Real.sqrt (2 * c) ≤ 1 / 2 := by nlinarith
  set q := Real.sqrt (2 * c) with hq
  unfold mnDA
  rcases lt_or_ge a 0 with ha | ha
  · rw [if_pos (by linarith)]
    unfold demandNew
    rw [if_pos]
    unfold BuysWithoutSearch nsPayoffNew
    rw [mn_search_neg c a ha, mn_meanVal]
    constructor <;> linarith
  · rw [mn_demand c a ha]
    by_cases h1 : a ≤ 1 / 2 ∧ a ^ 2 ≤ 2 * c
    · rw [if_pos h1, if_pos (by nlinarith [h1.2])]
    · rw [if_neg h1]
      have h1' : ¬ a ≤ q := by
        intro h; apply h1; exact ⟨by linarith, by nlinarith⟩
      rw [if_neg h1']
      by_cases h2 : a ≤ 1 ∧ 2 * c ≤ (1 - a) ^ 2
      · rw [if_pos h2, if_pos]
        by_contra hh
        push_neg at hh
        nlinarith [h2.2, h2.1]
      · rw [if_neg h2, if_neg]
        intro hh
        apply h2
        refine ⟨by linarith, by nlinarith⟩

lemma mn_demand_all' (c a : ℝ) (hc : 1 / 8 ≤ c) : demandNew c a = mnDB a := by
  unfold mnDB
  rcases lt_or_ge a 0 with ha | ha
  · rw [if_pos (by linarith)]
    unfold demandNew
    rw [if_pos]
    unfold BuysWithoutSearch nsPayoffNew
    rw [mn_search_neg c a ha, mn_meanVal]
    constructor <;> linarith
  · rw [mn_demand c a ha]
    by_cases h1 : a ≤ 1 / 2
    · rw [if_pos ⟨h1, by nlinarith⟩, if_pos h1]
    · rw [if_neg (fun h => h1 h.1), if_neg h1, if_neg]
      push_neg at h1
      rintro ⟨h2, h3⟩
      nlinarith

lemma mn_demandB_int (c p : ℝ) : demandB c p = ∫ a in (p - 1)..p, demandNew c a := by
  unfold demandB
  simp_rw [mn_buy]
  rw [intervalIntegral.integral_comp_sub_left (fun a => demandNew c a) p]
  simp

lemma mn_piece (f g : ℝ → ℝ) (x y : ℝ) (hxy : x ≤ y)
    (h : ∀ a, x < a → a ≤ y → f a = g a) :
    ∫ a in x..y, f a = ∫ a in x..y, g a := by
  apply intervalIntegral.integral_congr_ae
  refine Filter.Eventually.of_forall (fun a ha => ?_)
  rw [Set.uIoc_of_le hxy] at ha
  exact h a ha.1 ha.2

lemma mn_I1 (x y : ℝ) : ∫ a in x..y, (1 - a) = (y - x) - (y ^ 2 - x ^ 2) / 2 := by
  rw [intervalIntegral.integral_sub (by simp) (by simp)]
  simp [integral_id]

lemma mn_I0 (x y : ℝ) : ∫ _a in x..y, (1 : ℝ) = y - x := by simp

lemma mn_Iz (x y : ℝ) : ∫ _a in x..y, (0 : ℝ) = 0 := by simp

lemma mn_anti (q : ℝ) (hq : 0 ≤ q) : Antitone (mnDA q) := by
  intro a b hab
  unfold mnDA
  split_ifs <;> linarith

lemma mn_DA_int (q p : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1 / 2) :
    ∫ a in (p - 1)..p, mnDA q a =
      if p ≤ q then 1 else if p ≤ 1 - q then 1 + q ^ 2 / 2 - p ^ 2 / 2
      else if p ≤ 1 + q then 3 / 2 - p
      else if p ≤ 2 - q then (2 - p) ^ 2 / 2 - q ^ 2 / 2 else 0 := by
  have hi : ∀ x y : ℝ, IntervalIntegrable (mnDA q) MeasureTheory.volume x y :=
    fun x y => (mn_anti q hq0).intervalIntegrable
  by_cases h1 : p ≤ q
  · rw [if_pos h1]
    rw [mn_piece (mnDA q) (fun _ => 1) (p - 1) p (by linarith)
      (by intro a _ ha; simp only [mnDA]; rw [if_pos (by linarith)])]
    rw [mn_I0]; ring
  rw [if_neg h1]
  by_cases h2 : p ≤ 1 - q
  · rw [if_pos h2, ← intervalIntegral.integral_add_adjacent_intervals (hi (p - 1) q) (hi q p)]
    rw [mn_piece (mnDA q) (fun _ => 1) (p - 1) q (by linarith)
        (by intro a _ ha; simp only [mnDA]; rw [if_pos ha]),
      mn_piece (mnDA q) (fun a => 1 - a) q p (by linarith)
        (by intro a ha hb; simp only [mnDA]; rw [if_neg (by linarith), if_pos (by linarith)])]
    rw [mn_I0, mn_I1]; ring
  rw [if_neg h2]
  by_cases h3 : p ≤ 1 + q
  · rw [if_pos h3, ← intervalIntegral.integral_add_adjacent_intervals (hi (p - 1) q) (hi q p),
      ← intervalIntegral.integral_add_adjacent_intervals (hi q (1 - q)) (hi (1 - q) p)]
    rw [mn_piece (mnDA q) (fun _ => 1) (p - 1) q (by linarith)
        (by intro a _ ha; simp only [mnDA]; rw [if_pos ha]),
      mn_piece (mnDA q) (fun a => 1 - a) q (1 - q) (by linarith)
        (by intro a ha hb; simp only [mnDA]; rw [if_neg (by linarith), if_pos hb]),
      mn_piece (mnDA q) (fun _ => 0) (1 - q) p (by linarith)
        (by intro a ha hb; simp only [mnDA]; rw [if_neg (by linarith), if_neg (by linarith)])]
    rw [mn_I0, mn_I1, mn_Iz]; ring
  rw [if_neg h3]
  by_cases h4 : p ≤ 2 - q
  · rw [if_pos h4, ← intervalIntegral.integral_add_adjacent_intervals (hi (p - 1) (1 - q)) (hi (1 - q) p)]
    rw [mn_piece (mnDA q) (fun a => 1 - a) (p - 1) (1 - q) (by linarith)
        (by intro a ha hb; simp only [mnDA]; rw [if_neg (by linarith), if_pos hb]),
      mn_piece (mnDA q) (fun _ => 0) (1 - q) p (by linarith)
        (by intro a ha hb; simp only [mnDA]; rw [if_neg (by linarith), if_neg (by linarith)])]
    rw [mn_I1, mn_Iz]; ring
  · rw [if_neg h4]
    rw [mn_piece (mnDA q) (fun _ => 0) (p - 1) p (by linarith)
      (by intro a ha hb; simp only [mnDA]; rw [if_neg (by linarith), if_neg (by linarith)])]
    rw [mn_Iz]

lemma mn_DB_int (p : ℝ) :
    ∫ a in (p - 1)..p, mnDB a =
      if p ≤ 1 / 2 then 1 else if p ≤ 3 / 2 then 3 / 2 - p else 0 := by
  have hi : ∀ x y : ℝ, IntervalIntegrable mnDB MeasureTheory.volume x y := by
    intro x y
    apply Antitone.intervalIntegrable
    intro a b hab
    unfold mnDB
    split_ifs <;> linarith
  by_cases h1 : p ≤ 1 / 2
  · rw [if_pos h1]
    rw [mn_piece mnDB (fun _ => 1) (p - 1) p (by linarith)
      (by intro a _ ha; simp only [mnDB]; rw [if_pos (by linarith)])]
    rw [mn_I0]; ring
  rw [if_neg h1]
  by_cases h2 : p ≤ 3 / 2
  · rw [if_pos h2, ← intervalIntegral.integral_add_adjacent_intervals (hi (p - 1) (1 / 2)) (hi (1 / 2) p)]
    rw [mn_piece mnDB (fun _ => 1) (p - 1) (1 / 2) (by linarith)
        (by intro a _ ha; simp only [mnDB]; rw [if_pos ha]),
      mn_piece mnDB (fun _ => 0) (1 / 2) p (by linarith)
        (by intro a ha hb; simp only [mnDB]; rw [if_neg (by linarith)])]
    rw [mn_I0, mn_Iz]; ring
  · rw [if_neg h2]
    rw [mn_piece mnDB (fun _ => 0) (p - 1) p (by linarith)
      (by intro a ha hb; simp only [mnDB]; rw [if_neg (by linarith)])]
    rw [mn_Iz]

lemma mn_demandB_A (c p : ℝ) (hc : 0 ≤ c) (hc' : c ≤ 1 / 8) :
    demandB c p =
      if p ≤ Real.sqrt (2 * c) then 1
      else if p ≤ 1 - Real.sqrt (2 * c) then 1 + c - p ^ 2 / 2
      else if p ≤ 1 + Real.sqrt (2 * c) then 3 / 2 - p
      else if p ≤ 2 - Real.sqrt (2 * c) then (2 - p) ^ 2 / 2 - c else 0 := by
  have hq0 : 0 ≤ Real.sqrt (2 * c) := Real.sqrt_nonneg _
  have hq2 : Real.sqrt (2 * c) ^ 2 = 2 * c := Real.sq_sqrt (by linarith)
  have hq1 : Real.sqrt (2 * c) ≤ 1 / 2 := by nlinarith
  rw [mn_demandB_int]
  simp_rw [mn_demand_all c _ hc hc']
  rw [mn_DA_int _ p hq0 hq1, hq2]
  split_ifs <;> first | rfl | (congr 1; ring) | ring

lemma mn_demandB_B (c p : ℝ) (hc : 1 / 8 ≤ c) :
    demandB c p = if p ≤ 1 / 2 then 1 else if p ≤ 3 / 2 then 3 / 2 - p else 0 := by
  rw [mn_demandB_int]
  simp_rw [mn_demand_all' c _ hc]
  rw [mn_DB_int]

lemma mn_demandB_A2 (c p q : ℝ) (hc : 0 ≤ c) (hc' : c ≤ 1 / 8) (hq0 : 0 ≤ q)
    (hq2 : q ^ 2 = 2 * c) :
    demandB c p =
      if p ≤ q then 1
      else if p ≤ 1 - q then 1 + c - p ^ 2 / 2
      else if p ≤ 1 + q then 3 / 2 - p
      else if p ≤ 2 - q then (2 - p) ^ 2 / 2 - c else 0 := by
  have : q = Real.sqrt (2 * c) := by rw [← hq2]; exact (Real.sqrt_sq hq0).symm
  subst this
  exact mn_demandB_A c p hc hc'

lemma mn_w (w : ℝ) (h0 : 0 ≤ w) (h1 : w ≤ 1) : (2 - w) * (w ^ 2 / 2) ≤ 1 / 2 := by
  have : 0 ≤ 1 + w - w ^ 2 := by nlinarith [mul_nonneg h0 (sub_nonneg.2 h1)]
  nlinarith [mul_nonneg (sub_nonneg.2 h1) this]

lemma mn_prop_2_iii (c : ℝ) (hc : 1 / 32 < c) :
    IsGreatest (bundleRevenue c '' Set.Ici (0 : ℝ)) (9 / 16) ∧
    bundleRevenue c (3 / 4) = 9 / 16 := by
  rcases le_or_gt c (1 / 8) with hc8 | hc8
  · have hc0 : 0 ≤ c := by linarith
    obtain ⟨q, hq0, hq2⟩ : ∃ q : ℝ, 0 ≤ q ∧ q ^ 2 = 2 * c :=
      ⟨Real.sqrt (2 * c), Real.sqrt_nonneg _, Real.sq_sqrt (by linarith)⟩
    have hq1 : q ≤ 1 / 2 := by nlinarith
    have hq4 : 1 / 4 < q := by nlinarith
    have hat : bundleRevenue c (3 / 4) = 9 / 16 := by
      unfold bundleRevenue
      rw [mn_demandB_A2 c _ q hc0 hc8 hq0 hq2, if_neg (by linarith), if_neg (by linarith),
        if_pos (by linarith)]
      norm_num
    refine ⟨⟨⟨3 / 4, by norm_num, hat⟩, ?_⟩, hat⟩
    rintro y ⟨p, hp, rfl⟩
    have hp : 0 ≤ p := hp
    unfold bundleRevenue
    rw [mn_demandB_A2 c p q hc0 hc8 hq0 hq2]
    split_ifs with h1 h2 h3 h4
    · nlinarith
    · have hcc : c ≤ (1 - p) ^ 2 / 2 := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_left (show 1 + c - p ^ 2 / 2 ≤ 3 / 2 - p by nlinarith) hp,
        sq_nonneg (p - 3 / 4)]
    · nlinarith [sq_nonneg (p - 3 / 4)]
    · have hw : (2 - p) ^ 2 / 2 - c ≤ 1 / 4 := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_left hw hp]
    · norm_num
  · have hat : bundleRevenue c (3 / 4) = 9 / 16 := by
      unfold bundleRevenue
      rw [mn_demandB_B c _ hc8.le, if_neg (by norm_num), if_pos (by norm_num)]
      norm_num
    refine ⟨⟨⟨3 / 4, by norm_num, hat⟩, ?_⟩, hat⟩
    rintro y ⟨p, hp, rfl⟩
    have hp : 0 ≤ p := hp
    unfold bundleRevenue
    rw [mn_demandB_B c p hc8.le]
    split_ifs with h1 h2
    · linarith
    · nlinarith [sq_nonneg (p - 3 / 4)]
    · norm_num

lemma mn_prop_2_i (c : ℝ) (hc : 0 ≤ c) (hc' : c ≤ 2 - 3 * Real.sqrt 7 / 4) :
    IsGreatest (bundleRevenue c '' Set.Ici (0 : ℝ))
      (2 / 9 * (1 + c) * Real.sqrt (6 * (1 + c))) ∧
    bundleRevenue c (Real.sqrt (6 * (1 + c)) / 3) =
      2 / 9 * (1 + c) * Real.sqrt (6 * (1 + c)) := by
  obtain ⟨t, ht0, ht2, htd⟩ : ∃ t : ℝ, 0 ≤ t ∧ t ^ 2 = 7 ∧ Real.sqrt 7 = t :=
    ⟨_, Real.sqrt_nonneg _, Real.sq_sqrt (by norm_num), rfl⟩
  obtain ⟨S, hS0, hS2, hSd⟩ : ∃ S : ℝ, 0 ≤ S ∧ S ^ 2 = 6 * (1 + c) ∧
      Real.sqrt (6 * (1 + c)) = S :=
    ⟨_, Real.sqrt_nonneg _, Real.sq_sqrt (by linarith), rfl⟩
  obtain ⟨q, hq0, hq2⟩ : ∃ q : ℝ, 0 ≤ q ∧ q ^ 2 = 2 * c :=
    ⟨Real.sqrt (2 * c), Real.sqrt_nonneg _, Real.sq_sqrt (by linarith)⟩
  rw [htd] at hc'
  rw [hSd]
  have ht1 : 13 / 5 < t := by nlinarith
  have ht3 : t < 3 := by nlinarith
  have hc8 : c ≤ 1 / 8 := by nlinarith
  have hq_le : q ≤ (3 - t) / 2 := by
    by_contra h
    push_neg at h
    have := mul_self_lt_mul_self (by linarith : 0 ≤ (3 - t) / 2) h
    nlinarith
  have hq5 : q ≤ 1 / 5 := by linarith
  have hkey : 0 ≤ 2 * q ^ 2 - 6 * q + 1 := by
    nlinarith [mul_nonneg (sub_nonneg.2 hq_le) (show 0 ≤ (3 + t) / 2 - q by linarith)]
  have hS1 : 12 / 5 ≤ S := by nlinarith
  have hs2 : (S / 3) ^ 2 = 2 * (1 + c) / 3 := by nlinarith
  have hs_le : S / 3 ≤ 1 - q := by
    by_contra h
    push_neg at h
    have := mul_self_lt_mul_self (by linarith : 0 ≤ 1 - q) h
    nlinarith
  have hT : 2 / 9 * (1 + c) * S = (S / 3) ^ 3 := by
    have : (S / 3) ^ 3 = (S / 3) * (S / 3) ^ 2 := by ring
    rw [this, hs2]; ring
  have hat : bundleRevenue c (S / 3) = 2 / 9 * (1 + c) * S := by
    unfold bundleRevenue
    rw [mn_demandB_A2 c _ q hc hc8 hq0 hq2, if_neg (by linarith), if_pos hs_le, hs2]
    ring
  refine ⟨⟨⟨S / 3, by simp only [Set.mem_Ici]; linarith, hat⟩, ?_⟩, hat⟩
  rintro y ⟨p, hp, rfl⟩
  have hp : 0 ≤ p := hp
  have hs0 : 4 / 5 ≤ S / 3 := by linarith
  set s := S / 3 with hs
  have hc1 : 1 + c = 3 * s ^ 2 / 2 := by nlinarith
  have hcub : ∀ x : ℝ, 0 ≤ x → x * (1 + c - x ^ 2 / 2) ≤ s ^ 3 := by
    intro x hx
    rw [hc1]
    nlinarith [mul_nonneg (sq_nonneg (s - x)) (show 0 ≤ s + x / 2 by linarith)]
  have hT5 : 1 / 2 ≤ s ^ 3 := by nlinarith [mul_nonneg (by linarith : 0 ≤ s - 4 / 5) (by linarith : 0 ≤ s)]
  unfold bundleRevenue
  rw [mn_demandB_A2 c p q hc hc8 hq0 hq2, hT]
  split_ifs with h1 h2 h3 h4
  · linarith
  · exact hcub p hp
  · have h5 := hcub (1 - q) (by linarith)
    have h6 : (1 - q) * (1 + c - (1 - q) ^ 2 / 2) = (1 - q) * (3 / 2 - (1 - q)) := by
      have : c = q ^ 2 / 2 := by linarith
      rw [this]; ring
    have h7 : p * (3 / 2 - p) ≤ (1 - q) * (3 / 2 - (1 - q)) := by
      nlinarith [mul_nonneg (show 0 ≤ p - (1 - q) by linarith)
        (show 0 ≤ p + (1 - q) - 3 / 2 by linarith)]
    linarith
  · have hw : (2 - p) ^ 2 / 2 - c ≤ (2 - p) ^ 2 / 2 := by linarith
    have h7 := mul_le_mul_of_nonneg_left hw hp
    have h8 : 0 ≤ 2 - p := by linarith
    have h9 : 2 - p ≤ 1 := by linarith
    have h10 := mn_w (2 - p) h8 h9
    have h11 : (2 - (2 - p)) = p := by ring
    rw [h11] at h10
    linarith
  · nlinarith

lemma mn_prop_2_ii (c : ℝ) (hc : 2 - 3 * Real.sqrt 7 / 4 < c) (hc' : c ≤ 1 / 32) :
    IsGreatest (bundleRevenue c '' Set.Ici (0 : ℝ))
      (Real.sqrt (2 * c) / 2 - 2 * c + 1 / 2) ∧
    bundleRevenue c (1 - Real.sqrt (2 * c)) =
      Real.sqrt (2 * c) / 2 - 2 * c + 1 / 2 := by
  obtain ⟨t, ht0, ht2, htd⟩ : ∃ t : ℝ, 0 ≤ t ∧ t ^ 2 = 7 ∧ Real.sqrt 7 = t :=
    ⟨_, Real.sqrt_nonneg _, Real.sq_sqrt (by norm_num), rfl⟩
  rw [htd] at hc
  have ht1 : 13 / 5 < t := by nlinarith
  have ht3 : t < 3 := by nlinarith
  have hc0 : 0 ≤ c := by nlinarith
  obtain ⟨q, hq0, hq2, hqd⟩ : ∃ q : ℝ, 0 ≤ q ∧ q ^ 2 = 2 * c ∧ Real.sqrt (2 * c) = q :=
    ⟨Real.sqrt (2 * c), Real.sqrt_nonneg _, Real.sq_sqrt (by linarith), rfl⟩
  rw [hqd]
  have hc8 : c ≤ 1 / 8 := by linarith
  have hq4 : q ≤ 1 / 4 := by nlinarith
  have hq_ge : (3 - t) / 2 ≤ q := by
    by_contra h
    push_neg at h
    have := mul_self_lt_mul_self (by linarith : 0 ≤ q) h
    nlinarith
  have hkey : 2 * q ^ 2 - 6 * q + 1 ≤ 0 := by
    nlinarith [mul_nonneg (sub_nonneg.2 hq_ge) (show 0 ≤ (3 + t) / 2 - q by linarith)]
  have hcq : c = q ^ 2 / 2 := by linarith
  have hr : (1 - q) ^ 2 ≤ 2 * (1 + c) / 3 := by nlinarith
  have hT : q / 2 - 2 * c + 1 / 2 = (1 - q) * (3 / 2 - (1 - q)) := by rw [hcq]; ring
  have hat : bundleRevenue c (1 - q) = q / 2 - 2 * c + 1 / 2 := by
    unfold bundleRevenue
    rw [mn_demandB_A2 c _ q hc0 hc8 hq0 hq2, if_neg (by linarith), if_pos le_rfl, hT, hcq]
    ring
  refine ⟨⟨⟨1 - q, by simp; linarith, hat⟩, ?_⟩, hat⟩
  rintro y ⟨p, hp, rfl⟩
  have hp : 0 ≤ p := hp
  unfold bundleRevenue
  rw [mn_demandB_A2 c p q hc0 hc8 hq0 hq2]
  have hTq : 1 / 2 ≤ q / 2 - 2 * c + 1 / 2 := by nlinarith
  split_ifs with h1 h2 h3 h4
  · linarith
  · have hb : (p ^ 2 + p * (1 - q) + (1 - q) ^ 2) / 2 ≤ 1 + c := by nlinarith
    have := mul_nonneg (show 0 ≤ (1 - q) - p by linarith) (sub_nonneg.2 hb)
    have h6 : (1 - q) * (1 + c - (1 - q) ^ 2 / 2) = q / 2 - 2 * c + 1 / 2 := by
      rw [hcq]; ring
    nlinarith
  · have h7 : p * (3 / 2 - p) ≤ (1 - q) * (3 / 2 - (1 - q)) := by
      nlinarith [mul_nonneg (show 0 ≤ p - (1 - q) by linarith)
        (show 0 ≤ p + (1 - q) - 3 / 2 by linarith)]
    linarith
  · have hw : (2 - p) ^ 2 / 2 - c ≤ (2 - p) ^ 2 / 2 := by linarith
    have h7 := mul_le_mul_of_nonneg_left hw hp
    have h8 : 0 ≤ 2 - p := by linarith
    have h9 : 2 - p ≤ 1 := by linarith
    have h10 := mn_w (2 - p) h8 h9
    have h11 : (2 - (2 - p)) = p := by ring
    rw [h11] at h10
    linarith
  · nlinarith

theorem solution (c : ℝ) (hc : 1 / 32 < c) :
    IsGreatest (bundleRevenue c '' Set.Ici (0 : ℝ)) (9 / 16) ∧
    bundleRevenue c (3 / 4) = 9 / 16 := mn_prop_2_iii c hc
