-- Prove2me | solution 1 for FairShareAlmostAll.Slack.Supplement.cutoff_bound
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-15T21:38:08.89446+00:00
-- url     : https://prove2.me/submissions/01bb2556-e1a8-4305-a21d-f4dac89c96d7

import Mathlib
import Definitions.Def_AnyPriceShare_Bidding_Basic
import Definitions.Def_FairShareAlmostAll_Slack_FiniteAllocation
import Definitions.Def_FairShareAlmostAll_Slack_Instance
import Definitions.Def_FairShareAlmostAll_Slack_Buckets

open FairShareAlmostAll.Slack AnyPriceShare.Bidding

theorem FSCB_card_range (m A B : ℕ) (_hAB : A ≤ B) (hB : B ≤ m) :
    ((Finset.univ : Finset (Fin m)).filter (fun g => A ≤ g.val ∧ g.val < B)).card = B - A := by
  classical
  have hinj : Set.InjOn (fun g : Fin m => g.val)
      ((Finset.univ : Finset (Fin m)).filter (fun g => A ≤ g.val ∧ g.val < B)) :=
    fun a _ b _ h => Fin.ext h
  rw [← Finset.card_image_of_injOn hinj]
  have : ((Finset.univ : Finset (Fin m)).filter (fun g => A ≤ g.val ∧ g.val < B)).image
      (fun g : Fin m => g.val) = Finset.Ico A B := by
    ext x
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Ico]
    constructor
    · rintro ⟨g, hg, rfl⟩; exact hg
    · intro hx; exact ⟨⟨x, by omega⟩, hx, rfl⟩
  rw [this, Nat.card_Ico]

theorem solution {n m : ℕ} (X : Instance n m) (q : ℕ) (h : ConstructionAssumptions X q)
    (i : Fin n) (hi : i ∈ active X) :
    (cutoff X q i : ℝ) ≤ 2 + 2 * (q : ℝ) * Real.log (1 / X.entitlement i) := by
  classical
  obtain ⟨hn, hq, -, hcap, -, -⟩ := h
  set b := X.entitlement i with hb
  have hb0 : 0 < b := X.entitlement_pos i
  have hqR : (16:ℝ) ≤ q := by exact_mod_cast hq
  have hbcap : b ≤ 1 / (q:ℝ)^2 := hcap i
  have hb1 : b < 1 := by
    have : 1 / (q:ℝ)^2 < 1 := by
      rw [div_lt_one (by positivity)]; nlinarith
    linarith
  have hlog : 0 < Real.log (1 / b) := Real.log_pos (by rw [lt_div_iff₀ hb0]; linarith)
  set c := ⌈2 * (q:ℝ) * Real.log (1 / b)⌉₊ with hc
  have hcle : (c : ℝ) < 2 * (q:ℝ) * Real.log (1 / b) + 1 := Nat.ceil_lt_add_one (by positivity)
  have hcge : 2 * (q:ℝ) * Real.log (1 / b) ≤ c := Nat.le_ceil _
  set H := c + 1 with hH
  have hHle : (H : ℝ) ≤ 2 + 2 * (q:ℝ) * Real.log (1 / b) := by
    rw [hH]; push_cast; linarith
  -- cutoff ≤ any member, or the set is empty
  set Sset := {h : ℕ | 1 ≤ h ∧ h ≤ bucketCount q m ∧
    (h = bucketCount q m ∨ ((bucket q m h).card : ℝ) ≥ (q : ℝ) / b)} with hS
  have hcut : cutoff X q i = sInf Sset := rfl
  suffices hsuff : cutoff X q i ≤ H by
    have : (cutoff X q i : ℝ) ≤ H := by exact_mod_cast hsuff
    linarith
  rw [hcut]
  by_cases hBC : bucketCount q m ≤ H
  · by_cases h1 : 1 ≤ bucketCount q m
    · exact (Nat.sInf_le (show bucketCount q m ∈ Sset from ⟨h1, le_rfl, Or.inl rfl⟩)).trans hBC
    · have hemp : Sset = ∅ := by
        ext x; simp only [hS, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
        rintro ⟨hx1, hx2, -⟩; omega
      rw [hemp, Nat.sInf_empty]; exact Nat.zero_le _
  · push Not at hBC
    apply Nat.sInf_le (s := Sset)
    refine ⟨by omega, hBC.le, Or.inr ?_⟩
    -- H is not in the bucketCount set, so prefixSize q H < m
    have hnot : ¬ (0 < H ∧ m ≤ prefixSize q H) := by
      intro hmem
      have := Nat.sInf_le (s := {h : ℕ | 0 < h ∧ m ≤ prefixSize q h}) hmem
      unfold bucketCount at hBC
      omega
    have hpm : prefixSize q H < m := by
      by_contra hc'; exact hnot ⟨by omega, by omega⟩
    have hpre : prefixSize q H = prefixSize q (H - 1) + prescribedSize q H := by
      rw [hH]; simp only [Nat.add_sub_cancel]
      unfold prefixSize; rw [Finset.sum_range_succ]
    have hcard : (bucket q m H).card = prescribedSize q H := by
      unfold bucket
      rw [FSCB_card_range m _ _ (by omega) hpm.le]
      omega
    rw [hcard]
    have hps : (q:ℝ) * (1 + 1 / (q:ℝ)) ^ (H - 1) ≤ prescribedSize q H := Nat.le_ceil _
    have hH1 : H - 1 = c := by omega
    rw [hH1] at hps
    -- (1 + 1/q)^c ≥ 1/b
    have hq0 : (0:ℝ) < q := by linarith
    have hlog1 : 1 / (2 * (q:ℝ)) ≤ Real.log (1 + 1 / q) := by
      have h1 := Real.one_sub_inv_le_log_of_pos (show (0:ℝ) < 1 + 1 / q by positivity)
      have h2 : 1 / (2 * (q:ℝ)) ≤ 1 - (1 + 1 / (q:ℝ))⁻¹ := by
        rw [show 1 - (1 + 1 / (q:ℝ))⁻¹ = 1 / (q + 1) by field_simp; ring]
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        linarith
      linarith
    have hpow : 1 / b ≤ (1 + 1 / (q:ℝ)) ^ c := by
      rw [← Real.exp_log (show (0:ℝ) < 1 + 1 / q by positivity), ← Real.exp_nat_mul,
        ← Real.exp_log (show (0:ℝ) < 1 / b by positivity)]
      apply Real.exp_le_exp.mpr
      calc Real.log (1 / b) = (2 * (q:ℝ) * Real.log (1 / b)) * (1 / (2 * (q:ℝ))) := by
            field_simp
        _ ≤ (c : ℝ) * Real.log (1 + 1 / q) := by
            apply mul_le_mul hcge hlog1 (by positivity) (by positivity)
    have : (q:ℝ) / b = q * (1 / b) := by ring
    rw [this, ge_iff_le]
    calc (q:ℝ) * (1 / b) ≤ q * (1 + 1 / (q:ℝ)) ^ c := mul_le_mul_of_nonneg_left hpow hq0.le
      _ ≤ _ := hps
