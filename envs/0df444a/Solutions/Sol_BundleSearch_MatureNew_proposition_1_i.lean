-- Prove2me | solution 1 for BundleSearch.MatureNew.proposition_1_i
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T17:36:44.951008+00:00
-- url     : https://prove2.me/submissions/de7cb1ea-1f63-4f32-816e-6e6a1312218f

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

theorem solution (c : ℝ) (hc : 1 / 8 < c) :
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
