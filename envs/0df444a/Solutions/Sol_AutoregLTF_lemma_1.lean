-- Prove2me | solution 1 for AutoregLTF.lemma_1
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T07:27:58.849582+00:00
-- url     : https://prove2.me/submissions/698a38bd-5b13-41fa-9018-8ad3b5479793

import Mathlib
import Definitions.Def_AutoregLTF_state

section
set_option autoImplicit false
namespace AutoregLTF.Dev.Lemma1
open AutoregLTF

lemma row_eq (m : ℕ) (θ : ℕ → ℤ) (i t : ℕ) :
    (state m θ i t).row = fun j => decide (j = i) := by
  induction t with
  | zero => rfl
  | succ t ih => exact ih

lemma ptr_eq (m : ℕ) (θ : ℕ → ℤ) (i : ℕ) :
    ∀ t j : ℕ, 1 ≤ j → (state m θ i t).ptr j = decide (t + j = m + 1) := by
  intro t
  induction t with
  | zero => intro j hj; simp [state, init]
  | succ t ih =>
    intro j hj
    show (if j ≤ m then (state m θ i t).ptr (j + 1) else false) = _
    by_cases h : j ≤ m
    · rw [if_pos h, ih (j + 1) (by omega)]
      simp only [decide_eq_decide]; omega
    · rw [if_neg h]
      have : ¬ (t + 1 + j = m + 1) := by omega
      simp [this]

lemma out_rec (m : ℕ) (θ : ℕ → ℤ) (i t j : ℕ) :
    (state m θ i (t + 1)).out j =
      ((state m θ i t).out j || ((state m θ i t).ptr j && (state m θ i (t + 1)).test)) := by
  have h : (state m θ i (t + 1)).out j = decide (2 ≤ 2 * ((state m θ i t).out j).toNat +
      ((state m θ i t).ptr j).toNat + ((state m θ i (t + 1)).test).toNat) := rfl
  rw [h]
  generalize (state m θ i t).out j = a
  generalize (state m θ i t).ptr j = b
  generalize (state m θ i (t + 1)).test = c
  cases a <;> cases b <;> cases c <;> decide

lemma out_closed (m : ℕ) (lab : ℕ → ℕ → Bool) (i j : ℕ) (hj : j ∈ Finset.Icc 1 m) :
    ∀ t : ℕ, (∀ s, 2 ≤ s → s ≤ t → s ≤ m + 1 →
      (state m (enc m lab) i s).test = lab i (m + 2 - s)) →
      (state m (enc m lab) i t).out j = (decide (m + 1 < t + j) && lab i j) := by
  rw [Finset.mem_Icc] at hj
  intro t
  induction t with
  | zero =>
    intro _
    show false = _
    have : ¬ (m + 1 < 0 + j) := by omega
    rw [decide_eq_false this]; simp
  | succ t ih =>
    intro H
    rw [out_rec, ih (fun s h1 h2 h3 => H s h1 (by omega) h3), ptr_eq _ _ _ t j (by omega)]
    by_cases h : t + j = m + 1
    · have ht := H (t + 1) (by omega) le_rfl (by omega)
      have e : m + 2 - (t + 1) = j := by omega
      rw [ht, e]
      have h1 : ¬ (m + 1 < t + j) := by omega
      have h2 : m + 1 < t + 1 + j := by omega
      simp [h, h1, h2]
    · have : (m + 1 < t + 1 + j) ↔ (m + 1 < t + j) := by omega
      simp [h, this]

lemma low_lt (c : ℕ → ℤ) (hc : ∀ j, 0 ≤ c j ∧ c j ≤ 1) (n : ℕ) :
    ∑ j ∈ Finset.Icc 1 n, 2 ^ (j - 1) * c j + 1 ≤ 2 ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (by omega)]
    have := hc (n + 1)
    have h2 : (2 : ℤ) ^ (n + 1 - 1) = 2 ^ n := by simp
    rw [h2, pow_succ]
    nlinarith [pow_pos (show (0 : ℤ) < 2 by norm_num) n]

lemma test_eq (m : ℕ) (lab : ℕ → ℕ → Bool) (i : ℕ) (hi : i ∈ Finset.Icc 1 m) :
    ∀ s : ℕ, 2 ≤ s → s ≤ m + 1 → (state m (enc m lab) i s).test = lab i (m + 2 - s) := by
  intro s
  induction s using Nat.strong_induction_on with
  | _ s ih =>
  intro h2 hs
  obtain ⟨t, rfl⟩ : ∃ t, s = t + 1 := ⟨s - 1, by omega⟩
  obtain ⟨k, hk⟩ : ∃ k, k = m + 1 - t := ⟨_, rfl⟩
  have hout : ∀ j ∈ Finset.Icc 1 m, (state m (enc m lab) i t).out j =
      (decide (m + 1 < t + j) && lab i j) := fun j hj =>
    out_closed m lab i j hj t (fun s' h1 h2' h3 => ih s' (by omega) h1 h3)
  have hs1 : (state m (enc m lab) i (t + 1)).test = decide (0 ≤
      ∑ j ∈ Finset.Icc 1 m, enc m lab j * (((state m (enc m lab) i t).row j).toNat : ℤ) -
      ∑ j ∈ Finset.Icc 1 m, 2 ^ (j - 1) * ((((state m (enc m lab) i t).out j).toNat : ℤ) +
        (((state m (enc m lab) i t).ptr j).toNat : ℤ))) := rfl
  rw [hs1]
  have hkm : k ∈ Finset.Icc 1 m := by rw [Finset.mem_Icc]; omega
  have e1 : ∑ j ∈ Finset.Icc 1 m, enc m lab j * (((state m (enc m lab) i t).row j).toNat : ℤ)
      = enc m lab i := by
    rw [Finset.sum_eq_single_of_mem i hi (fun b _ hb => by simp [row_eq, hb])]
    simp [row_eq]
  set c : ℕ → ℤ := fun j => ((lab i j).toNat : ℤ) with hcdef
  have hc : ∀ j, 0 ≤ c j ∧ c j ≤ 1 := by
    intro j; simp only [hcdef]; cases lab i j <;> simp
  have e2 : ∑ j ∈ Finset.Icc 1 m, 2 ^ (j - 1) * ((((state m (enc m lab) i t).out j).toNat : ℤ) +
        (((state m (enc m lab) i t).ptr j).toNat : ℤ)) =
      ∑ j ∈ Finset.Icc 1 m, 2 ^ (j - 1) * (((decide (m + 1 < t + j) && lab i j).toNat : ℕ) : ℤ)
        + 2 ^ (k - 1) := by
    simp_rw [mul_add]
    rw [Finset.sum_add_distrib]
    congr 1
    · exact Finset.sum_congr rfl (fun j hj => by rw [hout j hj])
    · rw [Finset.sum_eq_single_of_mem k hkm]
      · rw [ptr_eq _ _ _ t k (by omega)]
        have : t + k = m + 1 := by omega
        simp [this]
      · intro b hb hbk
        rw [ptr_eq _ _ _ t b (by rw [Finset.mem_Icc] at hb; omega)]
        have : ¬ (t + b = m + 1) := by omega
        simp [this]
  have e3 : enc m lab i = ∑ j ∈ Finset.Icc 1 m, 2 ^ (j - 1) * c j := rfl
  have e4 : ∑ j ∈ Finset.Icc 1 m, 2 ^ (j - 1) * c j -
      ∑ j ∈ Finset.Icc 1 m, 2 ^ (j - 1) * (((decide (m + 1 < t + j) && lab i j).toNat : ℕ) : ℤ)
      = ∑ j ∈ Finset.Icc 1 k, 2 ^ (j - 1) * c j := by
    rw [← Finset.sum_sub_distrib]
    have hf : Finset.filter (fun j => j ≤ k) (Finset.Icc 1 m) = Finset.Icc 1 k := by
      ext j; simp only [Finset.mem_filter, Finset.mem_Icc]; omega
    rw [← hf, Finset.sum_filter]
    refine Finset.sum_congr rfl (fun j hj => ?_)
    rw [Finset.mem_Icc] at hj
    by_cases hjk : j ≤ k
    · have : ¬ (m + 1 < t + j) := by omega
      simp [this, hjk, hcdef]
    · have : m + 1 < t + j := by omega
      simp [this, hjk, hcdef]
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  have e5 : m + 2 - (t + 1) = k' + 1 := by omega
  rw [e1, e2, e3, e5, ← sub_sub, e4, Finset.sum_Icc_succ_top (by omega)]
  have hlow := low_lt c hc k'
  have hlow0 : 0 ≤ ∑ j ∈ Finset.Icc 1 k', 2 ^ (j - 1) * c j :=
    Finset.sum_nonneg (fun j _ => mul_nonneg (by positivity) (hc j).1)
  have h2' : (2 : ℤ) ^ (k' + 1 - 1) = 2 ^ k' := by simp
  rw [h2']
  cases hl : lab i (k' + 1)
  · have hck : c (k' + 1) = 0 := by simp [hcdef, hl]
    rw [hck]; simp; omega
  · have hck : c (k' + 1) = 1 := by simp [hcdef, hl]
    rw [hck]; simp; omega

lemma out_after (m : ℕ) (lab : ℕ → ℕ → Bool) (i : ℕ) (hi : i ∈ Finset.Icc 1 m)
    (j : ℕ) (hj : j ∈ Finset.Icc 1 m) (t : ℕ) (ht : m + 1 ≤ t) :
    (state m (enc m lab) i t).out j = lab i j := by
  rw [out_closed m lab i j hj t (fun s h1 h2 h3 => test_eq m lab i hi s h1 h3)]
  rw [Finset.mem_Icc] at hj
  have : m + 1 < t + j := by omega
  simp [this]

lemma out_small (m : ℕ) (lab : ℕ → ℕ → Bool) (i : ℕ)
    (j : ℕ) (hj : j ∈ Finset.Icc 1 m) (t : ℕ) (ht : t ≤ 1) :
    (state m (enc m lab) i t).out j = false := by
  rw [out_closed m lab i j hj t (fun s h1 h2 h3 => by omega)]
  rw [Finset.mem_Icc] at hj
  have : ¬ (m + 1 < t + j) := by omega
  simp [this]

lemma test_one (m : ℕ) (lab : ℕ → ℕ → Bool) (i : ℕ) (hi : i ∈ Finset.Icc 1 m) :
    (state m (enc m lab) i 1).test = true := by
  have hs1 : (state m (enc m lab) i 1).test = decide (0 ≤
      ∑ j ∈ Finset.Icc 1 m, enc m lab j * (((state m (enc m lab) i 0).row j).toNat : ℤ) -
      ∑ j ∈ Finset.Icc 1 m, 2 ^ (j - 1) * ((((state m (enc m lab) i 0).out j).toNat : ℤ) +
        (((state m (enc m lab) i 0).ptr j).toNat : ℤ))) := rfl
  rw [hs1]
  have e1 : ∑ j ∈ Finset.Icc 1 m, enc m lab j * (((state m (enc m lab) i 0).row j).toNat : ℤ)
      = enc m lab i := by
    rw [Finset.sum_eq_single_of_mem i hi (fun b _ hb => by simp [row_eq, hb])]
    simp [row_eq]
  have e2 : ∑ j ∈ Finset.Icc 1 m, 2 ^ (j - 1) * ((((state m (enc m lab) i 0).out j).toNat : ℤ) +
        (((state m (enc m lab) i 0).ptr j).toNat : ℤ)) = 0 := by
    refine Finset.sum_eq_zero (fun j hj => ?_)
    rw [Finset.mem_Icc] at hj
    have : (state m (enc m lab) i 0).ptr j = false := by
      rw [ptr_eq _ _ _ 0 j (by omega)]
      have : ¬ (0 + j = m + 1) := by omega
      rw [decide_eq_false this]
    have ho : (state m (enc m lab) i 0).out j = false := rfl
    rw [ho, this]; simp
  rw [e1, e2, sub_zero]
  have : 0 ≤ enc m lab i := Finset.sum_nonneg (fun j _ => mul_nonneg (by positivity) (by simp))
  simp [this]

end AutoregLTF.Dev.Lemma1

namespace AutoregLTF

open AutoregLTF.Dev.Lemma1 in
theorem chk_lemma_1 (m : ℕ) (hm : 2 ≤ m) (lab : ℕ → ℕ → Bool) :
    (∀ i ∈ Finset.Icc 1 m, ∀ j ∈ Finset.Icc 1 m, ∀ t : ℕ, m + 1 ≤ t →
      (state m (enc m lab) i t).out j = lab i j) ∧
    ∀ lab' : ℕ → ℕ → Bool, ∀ i ∈ Finset.Icc 1 m, ∀ t : ℕ, t ≤ 1 →
      (∀ j ∈ Finset.Icc 1 m,
        (state m (enc m lab) i t).row j = (state m (enc m lab') i t).row j) ∧
      (state m (enc m lab) i t).test = (state m (enc m lab') i t).test ∧
      (∀ j ∈ Finset.Icc 1 m,
        (state m (enc m lab) i t).out j = (state m (enc m lab') i t).out j) ∧
      (∀ j ∈ Finset.Icc 1 (m + 1),
        (state m (enc m lab) i t).ptr j = (state m (enc m lab') i t).ptr j) := by
  refine ⟨fun i hi j hj t ht => out_after m lab i hi j hj t ht, ?_⟩
  intro lab' i hi t ht
  refine ⟨fun j _ => by rw [row_eq, row_eq], ?_, fun j hj => ?_, fun j hj => ?_⟩
  · interval_cases t
    · rfl
    · rw [test_one m lab i hi, test_one m lab' i hi]
  · rw [out_small m lab i j hj t ht, out_small m lab' i j hj t ht]
  · rw [Finset.mem_Icc] at hj
    rw [ptr_eq _ _ _ t j (by omega), ptr_eq _ _ _ t j (by omega)]

end AutoregLTF
end

theorem solution : type_of% @AutoregLTF.chk_lemma_1 := @AutoregLTF.chk_lemma_1
