-- Prove2me | solution 2 for BundleSearch.MatureNew.theorem_1
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-27T09:48:22.236253+00:00
-- url     : https://prove2.me/submissions/342ed436-8e29-4209-9fa0-33c6a06a8a9b

import Mathlib
import Definitions.Def_BundleSearch_MatureNew_Model
import Theorems.Thm_BundleSearch_MatureNew_proposition_2_i
import Theorems.Thm_BundleSearch_MatureNew_proposition_2_ii
import Theorems.Thm_BundleSearch_MatureNew_proposition_2_iii

-- carved verbatim out of submission f4e31133-3c54-4e10-8536-01105fb236a6, lines 618-633

section
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

lemma mn_prop_1_i (c : ℝ) (hc : 1 / 8 < c) :
    IsGreatest (revenueNew c '' Set.Ici (0 : ℝ)) (1 / 2) ∧
    demandNew c (1 / 2) = 1 ∧ revenueNew c (1 / 2) = 1 / 2 := by
  have hd : demandNew c (1 / 2) = 1 := by
    rw [mn_demand c _ (by norm_num), if_pos ⟨le_rfl, by nlinarith⟩]
  have hr : revenueNew c (1 / 2) = 1 / 2 := by
    unfold revenueNew; rw [hd]; norm_num
  refine ⟨⟨⟨1 / 2, by norm_num, hr⟩, ?_⟩, hd, hr⟩
  rintro y ⟨p, hp, rfl⟩
  have hp : 0 ≤ p := hp
  unfold revenueNew
  rw [mn_demand c p hp]
  split_ifs with h1 h2
  · linarith [h1.1]
  · nlinarith [sq_nonneg (p - 1 / 2)]
  · norm_num

lemma mn_prop_1_ii (c : ℝ) (hc : 1 / 32 < c) (hc' : c ≤ 1 / 8) :
    IsGreatest (revenueNew c '' Set.Ici (0 : ℝ)) (Real.sqrt (2 * c)) ∧
    demandNew c (Real.sqrt (2 * c)) = 1 ∧
    revenueNew c (Real.sqrt (2 * c)) = Real.sqrt (2 * c) := by
  have hq0 : 0 ≤ Real.sqrt (2 * c) := Real.sqrt_nonneg _
  have hq2 : Real.sqrt (2 * c) ^ 2 = 2 * c := Real.sq_sqrt (by linarith)
  have hq1 : Real.sqrt (2 * c) ≤ 1 / 2 := by nlinarith
  have hq4 : 1 / 4 < Real.sqrt (2 * c) := by nlinarith
  have hd : demandNew c (Real.sqrt (2 * c)) = 1 := by
    rw [mn_demand c _ hq0, if_pos ⟨hq1, by rw [hq2]⟩]
  have hr : revenueNew c (Real.sqrt (2 * c)) = Real.sqrt (2 * c) := by
    unfold revenueNew; rw [hd]; ring
  refine ⟨⟨⟨_, hq0, hr⟩, ?_⟩, hd, hr⟩
  rintro y ⟨p, hp, rfl⟩
  have hp : 0 ≤ p := hp
  unfold revenueNew
  rw [mn_demand c p hp]
  split_ifs with h1 h2
  · have : p ≤ Real.sqrt (2 * c) := by nlinarith [h1.2]
    linarith
  · nlinarith [sq_nonneg (p - 1 / 2)]
  · linarith

lemma mn_prop_1_iii (c : ℝ) (hc : 0 ≤ c) (hc' : c ≤ 1 / 32) :
    IsGreatest (revenueNew c '' Set.Ici (0 : ℝ)) (1 / 4) ∧
    demandNew c (1 / 2) = 1 / 2 ∧ revenueNew c (1 / 2) = 1 / 4 := by
  have hd : demandNew c (1 / 2) = 1 / 2 := by
    rw [mn_demand c _ (by norm_num), if_neg (by rintro ⟨_, h⟩; nlinarith),
      if_pos ⟨by norm_num, by nlinarith⟩]
    norm_num
  have hr : revenueNew c (1 / 2) = 1 / 4 := by
    unfold revenueNew; rw [hd]; norm_num
  refine ⟨⟨⟨1 / 2, by norm_num, hr⟩, ?_⟩, hd, hr⟩
  rintro y ⟨p, hp, rfl⟩
  have hp : 0 ≤ p := hp
  unfold revenueNew
  rw [mn_demand c p hp]
  split_ifs with h1 h2
  · nlinarith [h1.2]
  · nlinarith [sq_nonneg (p - 1 / 2)]
  · norm_num

lemma mn_mature :
    revenueMature (1 / 2) = 1 / 4 ∧
    ∀ p : ℝ, 0 ≤ p → revenueMature p ≤ 1 / 4 := by
  constructor
  · unfold revenueMature
    rw [mn_probGe _ (by norm_num) (by norm_num)]; norm_num
  · intro p hp
    unfold revenueMature
    by_cases h : p ≤ 1
    · rw [mn_probGe p hp h]; nlinarith [sq_nonneg (p - 1 / 2)]
    · push_neg at h
      rw [mn_probGe_gt p h]; norm_num

lemma mn_sep (c R : ℝ) (hN : IsGreatest (revenueNew c '' Set.Ici (0 : ℝ)) R) :
    IsGreatest ((fun q : ℝ × ℝ => sepRevenue c q.1 q.2) ''
      (Set.Ici (0 : ℝ) ×ˢ Set.Ici (0 : ℝ))) (1 / 4 + R) := by
  obtain ⟨p2, hp2, hR⟩ := hN.1
  obtain ⟨hM1, hM2⟩ := mn_mature
  refine ⟨⟨(1 / 2, p2), ⟨show (0 : ℝ) ≤ 1 / 2 by norm_num, hp2⟩, ?_⟩, ?_⟩
  · simp only [sepRevenue]; rw [hM1, hR]
  · rintro y ⟨⟨p1, p2'⟩, ⟨h1, h2⟩, rfl⟩
    simp only [sepRevenue]
    have h3 := hM2 p1 h1
    have h4 := hN.2 ⟨p2', h2, rfl⟩
    linarith

lemma mn_t1_cases (c : ℝ) (hc : 0 ≤ c) :
    ∃ RB RN : ℝ, IsGreatest (bundleRevenue c '' Set.Ici (0 : ℝ)) RB ∧
      IsGreatest (revenueNew c '' Set.Ici (0 : ℝ)) RN ∧
      ((1 / 4 + RN ≤ RB ↔ c ≤ 25 / 512) ∧ (1 / 4 + RN < RB ↔ c < 25 / 512)) := by
  obtain ⟨t, ht0, ht2, htd⟩ : ∃ t : ℝ, 0 ≤ t ∧ t ^ 2 = 7 ∧ Real.sqrt 7 = t :=
    ⟨_, Real.sqrt_nonneg _, Real.sq_sqrt (by norm_num), rfl⟩
  have ht1 : 66 / 25 < t := by nlinarith
  have ht3 : t < 8 / 3 := by nlinarith
  rcases le_or_gt c (2 - 3 * Real.sqrt 7 / 4) with h0 | h0
  · have h0' : c ≤ 2 - 3 * t / 4 := by rw [htd] at h0; exact h0
    have hc32 : c ≤ 1 / 32 := by linarith
    refine ⟨_, 1 / 4, (BundleSearch.MatureNew.proposition_2_i c hc h0).1, (mn_prop_1_iii c hc hc32).1, ?_⟩
    obtain ⟨S, hS0, hS2, hSd⟩ : ∃ S : ℝ, 0 ≤ S ∧ S ^ 2 = 6 * (1 + c) ∧
        Real.sqrt (6 * (1 + c)) = S :=
      ⟨_, Real.sqrt_nonneg _, Real.sq_sqrt (by linarith), rfl⟩
    rw [hSd]
    have hS1 : 12 / 5 ≤ S := by nlinarith
    have hlt : 1 / 4 + 1 / 4 < 2 / 9 * (1 + c) * S := by nlinarith [mul_nonneg hc hS0]
    have hc' : c ≤ 25 / 512 := by linarith
    exact ⟨⟨fun _ => hc', fun _ => hlt.le⟩, ⟨fun _ => by linarith, fun _ => hlt⟩⟩
  · have h0' : 2 - 3 * t / 4 < c := by rw [htd] at h0; exact h0
    have hcpos : 0 < c := by linarith
    rcases le_or_gt c (1 / 32) with h1 | h1
    · refine ⟨_, 1 / 4, (BundleSearch.MatureNew.proposition_2_ii c h0 h1).1, (mn_prop_1_iii c hc h1).1, ?_⟩
      obtain ⟨q, hq0, hq2, hqd⟩ : ∃ q : ℝ, 0 ≤ q ∧ q ^ 2 = 2 * c ∧ Real.sqrt (2 * c) = q :=
        ⟨Real.sqrt (2 * c), Real.sqrt_nonneg _, Real.sq_sqrt (by linarith), rfl⟩
      rw [hqd]
      have hqpos : 0 < q := by
        rcases hq0.lt_or_eq with h | h
        · exact h
        · rw [← h] at hq2; linarith
      have hq4 : q ≤ 1 / 4 := by nlinarith
      have hlt : 1 / 4 + 1 / 4 < q / 2 - 2 * c + 1 / 2 := by nlinarith
      have hc' : c ≤ 25 / 512 := by linarith
      exact ⟨⟨fun _ => hc', fun _ => hlt.le⟩, ⟨fun _ => by linarith, fun _ => hlt⟩⟩
    · rcases le_or_gt c (1 / 8) with h2 | h2
      · obtain ⟨q, hq0, hq2, hqd⟩ : ∃ q : ℝ, 0 ≤ q ∧ q ^ 2 = 2 * c ∧ Real.sqrt (2 * c) = q :=
          ⟨Real.sqrt (2 * c), Real.sqrt_nonneg _, Real.sq_sqrt (by linarith), rfl⟩
        have hN := (mn_prop_1_ii c h1 h2).1
        rw [hqd] at hN
        refine ⟨9 / 16, q, (BundleSearch.MatureNew.proposition_2_iii c h1).1, hN, ?_, ?_⟩
        · constructor
          · intro h
            have : q ≤ 5 / 16 := by linarith
            nlinarith
          · intro h
            by_contra hh
            push_neg at hh
            nlinarith
        · constructor
          · intro h
            have : q < 5 / 16 := by linarith
            nlinarith
          · intro h
            by_contra hh
            push_neg at hh
            nlinarith
      · refine ⟨9 / 16, 1 / 2, (BundleSearch.MatureNew.proposition_2_iii c h1).1, (mn_prop_1_i c h2).1, ?_, ?_⟩
        · constructor
          · intro h; exfalso; norm_num at h
          · intro h; exfalso; linarith
        · constructor
          · intro h; exfalso; norm_num at h
          · intro h; exfalso; linarith

theorem solution (c : ℝ) (hc : 0 ≤ c) :
    (∃ RB : ℝ, IsGreatest (bundleRevenue c '' Set.Ici (0 : ℝ)) RB) ∧
    (∃ RS : ℝ, IsGreatest
      ((fun q : ℝ × ℝ => sepRevenue c q.1 q.2) ''
        (Set.Ici (0 : ℝ) ×ˢ Set.Ici (0 : ℝ))) RS) ∧
    ∀ RB RS : ℝ, IsGreatest (bundleRevenue c '' Set.Ici (0 : ℝ)) RB →
      IsGreatest ((fun q : ℝ × ℝ => sepRevenue c q.1 q.2) ''
        (Set.Ici (0 : ℝ) ×ˢ Set.Ici (0 : ℝ))) RS →
      ((RS ≤ RB ↔ c ≤ 25 / 512) ∧ (RS < RB ↔ c < 25 / 512)) := by
  obtain ⟨RB, RN, hB, hN, hiff⟩ := mn_t1_cases c hc
  have hS := mn_sep c RN hN
  refine ⟨⟨RB, hB⟩, ⟨_, hS⟩, ?_⟩
  intro RB' RS' h1 h2
  rw [← hB.unique h1, ← hS.unique h2]
  exact hiff

end
