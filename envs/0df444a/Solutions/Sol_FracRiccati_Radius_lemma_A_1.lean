-- Prove2me | solution 1 for FracRiccati.Radius.lemma_A_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-03T05:14:59.283984+00:00
-- url     : https://prove2.me/submissions/6e7b68fb-468b-43b5-9fb8-b95c36fdb146

import Mathlib

namespace Aux_FRR_A1

/-- Cell decomposition: the Riemann sum plus the integral over the middle cell is at most
the integral over `[0,1]`. -/
lemma cells (f : ℝ → ℝ)
    (hf_anti : AntitoneOn f (Set.Ioc (0 : ℝ) (1 / 2)))
    (hf_symm : ∀ x ∈ Set.Ioo (0 : ℝ) 1, f (1 - x) = f x)
    (hII : ∀ a b : ℝ, 0 ≤ a → a ≤ b → b ≤ 1 → IntervalIntegrable f MeasureTheory.volume a b)
    (k : ℕ) (hk : 1 ≤ k) :
    (1 / (k : ℝ)) * ∑ ℓ ∈ Finset.Ico 1 k, f ((ℓ : ℝ) / k) +
      ∫ u in ((k / 2 : ℕ) : ℝ) / k..((k / 2 + 1 : ℕ) : ℝ) / k, f u ≤ ∫ u in (0 : ℝ)..1, f u := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  set h := k / 2 with hh
  have hhk : h + 1 ≤ k := by omega
  have hcell : ∀ i ≤ k, 0 ≤ ((i : ℕ) : ℝ) / k ∧ ((i : ℕ) : ℝ) / k ≤ 1 := by
    intro i hi
    refine ⟨by positivity, ?_⟩
    rw [div_le_one hkR]; exact_mod_cast hi
  have hle : ∀ i : ℕ, ((i : ℕ) : ℝ) / k ≤ ((i + 1 : ℕ) : ℝ) / k := by
    intro i; apply div_le_div_of_nonneg_right _ hkR.le; push_cast; linarith
  have hlen : ∀ i : ℕ, ((i + 1 : ℕ) : ℝ) / k - ((i : ℕ) : ℝ) / k = 1 / k := by
    intro i; push_cast; ring
  let b : ℕ → ℝ := fun i => if i < h then (1 / (k : ℝ)) * f (((i + 1 : ℕ) : ℝ) / k)
    else if i = h then ∫ u in ((h : ℕ) : ℝ) / k..((h + 1 : ℕ) : ℝ) / k, f u
    else (1 / (k : ℝ)) * f ((i : ℕ) / (k : ℝ))
  have hpiece : ∀ i < k, b i ≤ ∫ u in ((i : ℕ) : ℝ) / k..((i + 1 : ℕ) : ℝ) / k, f u := by
    intro i hi
    have hI := hII _ _ (hcell i hi.le).1 (hle i) (hcell (i + 1) hi).2
    simp only [b]
    split_ifs with h1 h2
    · -- left half: f ≥ value at right endpoint
      have hr : ((i + 1 : ℕ) : ℝ) / k ≤ 1 / 2 := by
        rw [div_le_iff₀ hkR]; push_cast
        have : (i : ℝ) + 1 ≤ h := by exact_mod_cast h1
        have : (2 : ℝ) * h ≤ k := by exact_mod_cast (by omega : 2 * h ≤ k)
        linarith
      have hr0 : 0 < ((i + 1 : ℕ) : ℝ) / k := by positivity
      calc (1 / (k : ℝ)) * f (((i + 1 : ℕ) : ℝ) / k)
          = ∫ u in ((i : ℕ) : ℝ) / k..((i + 1 : ℕ) : ℝ) / k, f (((i + 1 : ℕ) : ℝ) / k) := by
            rw [intervalIntegral.integral_const, hlen, smul_eq_mul]
        _ ≤ _ := by
            apply intervalIntegral.integral_mono_on_of_le_Ioo (hle i) intervalIntegrable_const hI
            intro x hx
            obtain ⟨hx1, hx2⟩ := hx
            have hx0 : 0 < x := lt_of_le_of_lt (hcell i hi.le).1 hx1
            exact hf_anti ⟨hx0, by linarith⟩ ⟨hr0, hr⟩ hx2.le
    · subst h2; exact le_rfl
    · -- right half: f ≥ value at left endpoint, by symmetry
      have hgt : h + 1 ≤ i := by omega
      have hl : 1 / 2 ≤ ((i : ℕ) : ℝ) / k := by
        rw [le_div_iff₀ hkR]
        have h3 : ((h + 1 : ℕ) : ℝ) ≤ i := by exact_mod_cast hgt
        have h4 : (k : ℝ) < 2 * ((h + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : k < 2 * (h + 1))
        linarith
      have hl1 : ((i : ℕ) : ℝ) / k < 1 := by rw [div_lt_one hkR]; exact_mod_cast hi
      calc (1 / (k : ℝ)) * f ((i : ℕ) / (k : ℝ))
          = ∫ u in ((i : ℕ) : ℝ) / k..((i + 1 : ℕ) : ℝ) / k, f ((i : ℕ) / (k : ℝ)) := by
            rw [intervalIntegral.integral_const, hlen, smul_eq_mul]
        _ ≤ _ := by
            apply intervalIntegral.integral_mono_on_of_le_Ioo (hle i) intervalIntegrable_const hI
            intro x hx
            obtain ⟨hx1, hx2⟩ := hx
            have hx1' : x < 1 := lt_of_lt_of_le hx2 (hcell (i + 1) hi).2
            have hi0 : 0 < ((i : ℕ) : ℝ) / k := by linarith
            rw [← hf_symm x ⟨by linarith, hx1'⟩, ← hf_symm _ ⟨hi0, hl1⟩]
            exact hf_anti ⟨by linarith, by linarith⟩ ⟨by linarith, by linarith⟩ (by linarith)
  have hsplit := intervalIntegral.sum_integral_adjacent_intervals (μ := MeasureTheory.volume)
    (f := f) (a := fun i : ℕ => ((i : ℕ) : ℝ) / k) (n := k)
    (fun i hi => hII _ _ (hcell i hi.le).1 (hle i) (hcell (i + 1) hi).2)
  simp only [Nat.cast_zero, zero_div] at hsplit
  rw [div_self hkR.ne'] at hsplit
  rw [← hsplit]
  have hsum : ∑ i ∈ Finset.range k, b i =
      (1 / (k : ℝ)) * ∑ ℓ ∈ Finset.Ico 1 k, f ((ℓ : ℝ) / k) +
        ∫ u in ((h : ℕ) : ℝ) / k..((h + 1 : ℕ) : ℝ) / k, f u := by
    rw [Finset.range_eq_Ico, ← Finset.sum_Ico_consecutive _ (Nat.zero_le h) (by omega : h ≤ k),
      Finset.sum_eq_sum_Ico_succ_bot (by omega : h < k),
      ← Finset.sum_Ico_consecutive _ (by omega : 1 ≤ h + 1) hhk, mul_add, Finset.mul_sum,
      Finset.mul_sum]
    have e1 : ∑ i ∈ Finset.Ico 0 h, b i =
        ∑ ℓ ∈ Finset.Ico 1 (h + 1), (1 / (k : ℝ)) * f ((ℓ : ℝ) / k) := by
      rw [show (1 : ℕ) = 0 + 1 from rfl, ← Finset.sum_Ico_add']
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.mem_Ico] at hi
      simp only [b, if_pos hi.2]
    have e2 : b h = ∫ u in ((h : ℕ) : ℝ) / k..((h + 1 : ℕ) : ℝ) / k, f u := by simp [b]
    have e3 : ∑ i ∈ Finset.Ico (h + 1) k, b i =
        ∑ ℓ ∈ Finset.Ico (h + 1) k, (1 / (k : ℝ)) * f ((ℓ : ℝ) / k) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.mem_Ico] at hi
      simp only [b, if_neg (by omega : ¬ i < h), if_neg (by omega : ¬ i = h)]
    rw [e1, e2, e3]; ring
  rw [← hsum]
  exact Finset.sum_le_sum fun i hi => hpiece i (Finset.mem_range.mp hi)

end Aux_FRR_A1

open Aux_FRR_A1 in
theorem solution (f : ℝ → ℝ)
    (hf_nonneg : ∀ x ∈ Set.Ioo (0 : ℝ) 1, 0 ≤ f x)
    (hf_anti : AntitoneOn f (Set.Ioc (0 : ℝ) (1 / 2)))
    (hf_symm : ∀ x ∈ Set.Ioo (0 : ℝ) 1, f (1 - x) = f x)
    (hf_int : MeasureTheory.IntegrableOn f (Set.Ioo (0 : ℝ) 1)) :
    IsLeast (f '' Set.Ioo (0 : ℝ) 1) (f (1 / 2)) ∧
    ∀ k : ℕ, 1 ≤ k →
      (1 - 1 / (k : ℝ)) * f (1 / 2) ≤ (1 / (k : ℝ)) * ∑ ℓ ∈ Finset.Ico 1 k, f ((ℓ : ℝ) / k) ∧
      (1 / (k : ℝ)) * ∑ ℓ ∈ Finset.Ico 1 k, f ((ℓ : ℝ) / k) ≤
        (∫ u in (0 : ℝ)..1, f u)
          - (if Even k then (∫ u in (1 / 2 : ℝ)..(1 / 2 + 1 / (k : ℝ)), f u) else 0)
          - (if Odd k then (∫ u in ((k : ℝ) - 1) / (2 * k)..((k : ℝ) + 1) / (2 * k), f u)
              else 0) := by
  have hmin : ∀ x ∈ Set.Ioo (0 : ℝ) 1, f (1 / 2) ≤ f x := by
    intro x hx
    obtain ⟨h0, h1⟩ := hx
    rcases le_or_gt x (1 / 2) with hx2 | hx2
    · exact hf_anti ⟨h0, hx2⟩ ⟨by norm_num, le_rfl⟩ hx2
    · rw [← hf_symm x ⟨h0, h1⟩]
      exact hf_anti ⟨by linarith, by linarith⟩ ⟨by norm_num, le_rfl⟩ (by linarith)
  have hII : ∀ a b : ℝ, 0 ≤ a → a ≤ b → b ≤ 1 → IntervalIntegrable f MeasureTheory.volume a b := by
    intro a b ha hab hb
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab,
      integrableOn_Ioc_iff_integrableOn_Ioo]
    exact hf_int.mono_set (Set.Ioo_subset_Ioo ha hb)
  refine ⟨⟨⟨1 / 2, ⟨by norm_num, by norm_num⟩, rfl⟩, ?_⟩, fun k hk => ⟨?_, ?_⟩⟩
  · rintro y ⟨x, hx, rfl⟩; exact hmin x hx
  · have hkR : (0 : ℝ) < k := by exact_mod_cast hk
    have hs : ∑ ℓ ∈ Finset.Ico 1 k, f (1 / 2) ≤ ∑ ℓ ∈ Finset.Ico 1 k, f ((ℓ : ℝ) / k) := by
      apply Finset.sum_le_sum
      intro ℓ hℓ
      rw [Finset.mem_Ico] at hℓ
      apply hmin
      constructor
      · have : (0 : ℝ) < ℓ := by exact_mod_cast hℓ.1
        positivity
      · rw [div_lt_one hkR]; exact_mod_cast hℓ.2
    rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul, Nat.cast_sub hk] at hs
    have : (1 - 1 / (k : ℝ)) * f (1 / 2) = (1 / (k : ℝ)) * (((k : ℝ) - ((1 : ℕ) : ℝ)) * f (1 / 2)) := by
      field_simp; push_cast; ring
    rw [this]
    exact mul_le_mul_of_nonneg_left hs (by positivity)
  · have hc := cells f hf_anti hf_symm hII k hk
    have hkR : (0 : ℝ) < k := by exact_mod_cast hk
    rcases Nat.even_or_odd k with he | ho
    · have hno : ¬ Odd k := Nat.not_odd_iff_even.mpr he
      rw [if_pos he, if_neg hno, sub_zero]
      obtain ⟨r, hr⟩ := he
      have h2 : k / 2 = r := by omega
      have ea : ((k / 2 : ℕ) : ℝ) / k = 1 / 2 := by
        rw [h2, hr]; push_cast
        have : (0 : ℝ) < r := by have : 0 < r := by omega
                                 exact_mod_cast this
        field_simp; ring
      have eb : ((k / 2 + 1 : ℕ) : ℝ) / k = 1 / 2 + 1 / k := by
        rw [h2]; push_cast; rw [hr]; push_cast
        have : (0 : ℝ) < r := by have : 0 < r := by omega
                                 exact_mod_cast this
        field_simp; ring
      rw [ea, eb] at hc
      linarith
    · have hne : ¬ Even k := Nat.not_even_iff_odd.mpr ho
      rw [if_neg hne, if_pos ho, sub_zero]
      obtain ⟨r, hr⟩ := ho
      have h2 : k / 2 = r := by omega
      have ea : ((k / 2 : ℕ) : ℝ) / k = ((k : ℝ) - 1) / (2 * k) := by
        rw [h2, hr]; push_cast; field_simp; ring
      have eb : ((k / 2 + 1 : ℕ) : ℝ) / k = ((k : ℝ) + 1) / (2 * k) := by
        rw [h2]; push_cast; rw [hr]; push_cast; field_simp; ring
      rw [ea, eb] at hc
      linarith
