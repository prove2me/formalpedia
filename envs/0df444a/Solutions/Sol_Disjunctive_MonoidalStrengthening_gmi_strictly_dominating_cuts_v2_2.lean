-- Prove2me | solution 2 for Disjunctive.MonoidalStrengthening.gmi_strictly_dominating_cuts_v2
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-12T23:09:16.202974+00:00
-- url     : https://prove2.me/submissions/82fbd5ff-7edc-45d1-a6f5-6ece710aa8aa

import Mathlib
import Definitions.Def_Disjunctive_MonoidalStrengthening_Basic



namespace Disjunctive.MonoidalStrengthening

/-- middle-case coefficient dominates `-a/(1-a0)`. -/
lemma gmiB_mid_ge (a0 b : ℝ) (ha0 : 0 < a0) (ha0' : a0 < 1) (hb1 : a0 - 1 ≤ b) :
    -b / (1 - a0) ≤ min ((b - (⌊b⌋ : ℝ)) / a0) ((-b + (⌈b⌉ : ℝ)) / (1 - a0)) := by
  have h1 : (0:ℝ) < 1 - a0 := by linarith
  have hf1 := Int.floor_le b
  have hf2 := Int.lt_floor_add_one b
  have hc1 := Int.le_ceil b
  have hc0 : (0 : ℤ) ≤ ⌈b⌉ := by
    have : (-1 : ℝ) < (⌈b⌉ : ℝ) := by linarith
    have : (-1 : ℤ) < ⌈b⌉ := by exact_mod_cast this
    omega
  have hc0' : (0:ℝ) ≤ (⌈b⌉ : ℝ) := by exact_mod_cast hc0
  apply le_min
  · rw [div_le_div_iff₀ h1 ha0]
    rcases le_or_gt 0 b with hb | hb
    · nlinarith
    · have hfl : ⌊b⌋ = -1 := by
        have : ⌊b⌋ < 0 := by
          have : (⌊b⌋ : ℝ) < 0 := by linarith
          exact_mod_cast this
        have : (-2 : ℝ) < (⌊b⌋ : ℝ) := by linarith
        have : (-2 : ℤ) < ⌊b⌋ := by exact_mod_cast this
        omega
      rw [hfl]; push_cast; nlinarith
  · rw [div_le_div_iff_of_pos_right h1]; linarith

/-- per-coordinate bound used when the big set carries no mass. -/
lemma gmiB_mono_choice (a0 b : ℝ) (ha0 : 0 < a0) (ha0' : a0 < 1) :
    ∃ m : ℤ, (b + m) / a0 ≤ min ((b - (⌊b⌋ : ℝ)) / a0) ((-b + (⌈b⌉ : ℝ)) / (1 - a0)) ∧
      -(b + m) / (1 - a0) ≤ min ((b - (⌊b⌋ : ℝ)) / a0) ((-b + (⌈b⌉ : ℝ)) / (1 - a0)) := by
  have h1 : (0:ℝ) < 1 - a0 := by linarith
  have hf1 := Int.floor_le b
  have hc1 := Int.le_ceil b
  have hA : 0 ≤ (b - (⌊b⌋ : ℝ)) / a0 := div_nonneg (by linarith) ha0.le
  have hB : 0 ≤ (-b + (⌈b⌉ : ℝ)) / (1 - a0) := div_nonneg (by linarith) h1.le
  rcases le_total ((b - (⌊b⌋ : ℝ)) / a0) ((-b + (⌈b⌉ : ℝ)) / (1 - a0)) with h | h
  · refine ⟨-⌊b⌋, ?_, ?_⟩
    · rw [min_eq_left h]; push_cast; rw [← sub_eq_add_neg]
    · rw [min_eq_left h]
      have : -(b + ((-⌊b⌋ : ℤ) : ℝ)) / (1 - a0) ≤ 0 := by
        apply div_nonpos_of_nonpos_of_nonneg _ h1.le; push_cast; linarith
      linarith
  · refine ⟨-⌈b⌉, ?_, ?_⟩
    · rw [min_eq_right h]
      have : (b + ((-⌈b⌉ : ℤ) : ℝ)) / a0 ≤ 0 := by
        apply div_nonpos_of_nonpos_of_nonneg _ ha0.le; push_cast; linarith
      linarith
    · rw [min_eq_right h]; push_cast; apply le_of_eq; ring_nf

theorem gmiB_plus_core {n : ℕ} (a0 : ℝ) (a : Fin n → ℝ) (J1 : Finset (Fin n))
    (ha0 : 0 < a0) (ha0' : a0 < 1)
    (x : Fin n → ℝ) (hx_nonneg : 0 ≤ x) (hx_int : ∀ j ∈ J1, ∃ k : ℤ, x j = (k : ℝ))
    (hy : a0 - ∑ j, a j * x j = 0 ∨ a0 - ∑ j, a j * x j = 1) :
    1 ≤ ∑ j, AlphaPlus a0 a J1 j * x j := by
  classical
  have h1 : (0:ℝ) < 1 - a0 := by linarith
  set u := ∑ j, a j * x j with hu
  by_cases hbig : ∃ j, (j ∈ J1 ∧ 1 < a j) ∧ x j ≠ 0
  · obtain ⟨j0, ⟨hj0J, hj0a⟩, hj0x⟩ := hbig
    obtain ⟨k0, hk0⟩ := hx_int j0 hj0J
    have hxj0 : 1 ≤ x j0 := by
      have hpos : 0 < x j0 := lt_of_le_of_ne (hx_nonneg j0) (Ne.symm hj0x)
      rw [hk0] at hpos ⊢
      have : (0:ℤ) < k0 := by exact_mod_cast hpos
      exact_mod_cast this
    -- per-coordinate bound
    let ind : Fin n → ℝ := fun j => if j ∈ J1 ∧ 1 < a j then x j else 0
    have hper : ∀ j, (-(a j * x j) + ind j) / (1 - a0) ≤ AlphaPlus a0 a J1 j * x j := by
      intro j
      have hxj := hx_nonneg j
      simp only [ind, AlphaPlus]
      split_ifs with hA hB
      · rw [div_mul_eq_mul_div]; apply le_of_eq; congr 1; ring
      · rw [add_zero, show -(a j * x j) / (1 - a0) = (-(a j) / (1 - a0)) * x j by ring]
        exact mul_le_mul_of_nonneg_right (gmiB_mid_ge a0 (a j) ha0 ha0' hB.2.1) hxj
      · rw [add_zero, show -(a j * x j) / (1 - a0) = (-(a j) / (1 - a0)) * x j by ring]
        exact mul_le_mul_of_nonneg_right (le_max_right _ _) hxj
    have hsum := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => hper j)
    rw [← Finset.sum_div, Finset.sum_add_distrib, Finset.sum_neg_distrib] at hsum
    have hind : 1 ≤ ∑ j, ind j := by
      have hnn : ∀ j ∈ Finset.univ, 0 ≤ ind j := by
        intro j _; simp only [ind]; split_ifs
        · exact hx_nonneg j
        · exact le_rfl
      have := Finset.single_le_sum hnn (Finset.mem_univ j0)
      have : ind j0 = x j0 := by simp [ind, hj0J, hj0a]
      linarith
    have hule : u ≤ a0 := by rcases hy with h | h <;> linarith
    have : 1 ≤ (-u + ∑ j, ind j) / (1 - a0) := by
      rw [le_div_iff₀ h1]; linarith
    linarith
  · push_neg at hbig
    -- choose monoid shifts
    have hch : ∀ j, ∃ m : ℤ, (j ∉ J1 → m = 0) ∧
        ((a j + m) * x j / a0 ≤ AlphaPlus a0 a J1 j * x j) ∧
        (-(a j + m) * x j / (1 - a0) ≤ AlphaPlus a0 a J1 j * x j) := by
      intro j
      have hxj := hx_nonneg j
      by_cases hB : j ∈ J1 ∧ 1 < a j
      · refine ⟨0, fun h => absurd hB.1 h, ?_, ?_⟩ <;> simp [hbig j hB]
      by_cases hM : j ∈ J1 ∧ a0 - 1 ≤ a j ∧ a j ≤ 1
      · obtain ⟨m, hm1, hm2⟩ := gmiB_mono_choice a0 (a j) ha0 ha0'
        refine ⟨m, fun h => absurd hM.1 h, ?_, ?_⟩
        · simp only [AlphaPlus, if_neg hB, if_pos hM]
          rw [mul_div_right_comm]; exact mul_le_mul_of_nonneg_right hm1 hxj
        · simp only [AlphaPlus, if_neg hB, if_pos hM]
          rw [mul_div_right_comm]; exact mul_le_mul_of_nonneg_right hm2 hxj
      · refine ⟨0, fun _ => rfl, ?_, ?_⟩
        · simp only [AlphaPlus, if_neg hB, if_neg hM]
          push_cast; rw [add_zero, mul_div_right_comm]
          exact mul_le_mul_of_nonneg_right (le_max_left _ _) hxj
        · simp only [AlphaPlus, if_neg hB, if_neg hM]
          push_cast; rw [add_zero, mul_div_right_comm]
          exact mul_le_mul_of_nonneg_right (le_max_right _ _) hxj
    choose m hm0 hmA hmB using hch
    let kf : Fin n → ℤ := fun j => if h : j ∈ J1 then Classical.choose (hx_int j h) else 0
    have hmx : ∀ j, (m j : ℝ) * x j = ((m j * kf j : ℤ) : ℝ) := by
      intro j
      by_cases hj : j ∈ J1
      · simp only [kf, dif_pos hj]; push_cast
        rw [← Classical.choose_spec (hx_int j hj)]
      · simp [hm0 j hj]
    set T : ℤ := ∑ j, m j * kf j with hT
    have hsumT : ∑ j, (a j + m j) * x j = u + T := by
      rw [hu, hT]; push_cast
      rw [← Finset.sum_add_distrib]; apply Finset.sum_congr rfl
      intro j _; have := hmx j; push_cast at this; rw [← this]; ring
    -- y is 0 or 1
    obtain ⟨yv, hyv, hyz⟩ : ∃ yv : ℤ, (yv = 0 ∨ yv = 1) ∧ u = a0 - yv := by
      rcases hy with h | h
      · exact ⟨0, Or.inl rfl, by push_cast; linarith⟩
      · exact ⟨1, Or.inr rfl, by push_cast; linarith⟩
    rcases le_or_gt yv T with hN | hN
    · have hsA := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => hmA j)
      rw [← Finset.sum_div, hsumT, hyz] at hsA
      have hN' : (yv : ℝ) ≤ T := by exact_mod_cast hN
      have : 1 ≤ (a0 - yv + T) / a0 := by rw [le_div_iff₀ ha0]; linarith
      linarith
    · have hsB := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => hmB j)
      rw [← Finset.sum_div] at hsB
      have he : ∑ j, -(a j + m j) * x j = -(u + T) := by
        rw [← hsumT, ← Finset.sum_neg_distrib]; apply Finset.sum_congr rfl; intro j _; ring
      rw [he, hyz] at hsB
      have hN1 : T + 1 ≤ yv := hN
      have hN' : (T : ℝ) + 1 ≤ yv := by exact_mod_cast hN1
      have : 1 ≤ -(a0 - yv + T) / (1 - a0) := by rw [le_div_iff₀ h1]; linarith
      linarith

lemma gmiB_alphaMinus_eq (a0 : ℝ) {n : ℕ} (a : Fin n → ℝ) (J1 : Finset (Fin n)) (j : Fin n) :
    AlphaMinus a0 a J1 j = AlphaPlus (1 - a0) (fun i => -a i) J1 j := by
  unfold AlphaMinus AlphaPlus
  dsimp only
  rw [show (1:ℝ) - (1 - a0) = a0 by ring, Int.floor_neg, Int.ceil_neg]
  by_cases h1 : j ∈ J1 ∧ a j < -1
  · rw [if_pos h1, if_pos ⟨h1.1, by linarith [h1.2]⟩]; ring
  · rw [if_neg h1, if_neg (show ¬(j ∈ J1 ∧ 1 < -a j) from fun h => h1 ⟨h.1, by linarith [h.2]⟩)]
    by_cases h2 : j ∈ J1 ∧ -1 ≤ a j ∧ a j ≤ a0
    · rw [if_pos h2, if_pos (show j ∈ J1 ∧ 1 - a0 - 1 ≤ -a j ∧ -a j ≤ 1 from
        ⟨h2.1, by linarith [h2.2.2], by linarith [h2.2.1]⟩), min_comm]
      push_cast
      congr 1 <;> ring
    · rw [if_neg h2, if_neg (show ¬(j ∈ J1 ∧ 1 - a0 - 1 ≤ -a j ∧ -a j ≤ 1) from
        fun h => h2 ⟨h.1, by linarith [h.2.2], by linarith [h.2.1]⟩),
        max_comm]
      congr 1 <;> ring

theorem gmiB_core {n : ℕ} (a0 : ℝ) (a : Fin n → ℝ) (J1 : Finset (Fin n))
    (ha0 : 0 < a0) (ha0' : a0 < 1)
    (x : Fin n → ℝ) (hx_nonneg : 0 ≤ x) (hx_int : ∀ j ∈ J1, ∃ k : ℤ, x j = (k : ℝ))
    (hy : a0 - ∑ j, a j * x j = 0 ∨ a0 - ∑ j, a j * x j = 1) :
    1 ≤ ∑ j, AlphaPlus a0 a J1 j * x j ∧ 1 ≤ ∑ j, AlphaMinus a0 a J1 j * x j := by
  refine ⟨gmiB_plus_core a0 a J1 ha0 ha0' x hx_nonneg hx_int hy, ?_⟩
  simp only [gmiB_alphaMinus_eq]
  apply gmiB_plus_core (1 - a0) (fun i => -a i) J1 (by linarith) (by linarith) x hx_nonneg hx_int
  have : ∑ j, (fun i => -a i) j * x j = -∑ j, a j * x j := by
    rw [← Finset.sum_neg_distrib]; apply Finset.sum_congr rfl; intro j _; ring
  rw [this]
  rcases hy with h | h
  · right; linarith
  · left; linarith

end Disjunctive.MonoidalStrengthening

open Disjunctive.MonoidalStrengthening


theorem solution {n : ℕ} (a0 : ℝ) (a : Fin n → ℝ) (J1 : Finset (Fin n))
    (ha0 : 0 < a0) (ha0' : a0 < 1)
    (x : Fin n → ℝ) (hx_nonneg : 0 ≤ x) (hx_int : ∀ j ∈ J1, ∃ k : ℤ, x j = (k : ℝ))
    (hy : a0 - ∑ j, a j * x j = 0 ∨ a0 - ∑ j, a j * x j = 1) :
    1 ≤ ∑ j, AlphaPlus a0 a J1 j * x j ∧ 1 ≤ ∑ j, AlphaMinus a0 a J1 j * x j := by
  exact gmiB_core a0 a J1 ha0 ha0' x hx_nonneg hx_int hy
