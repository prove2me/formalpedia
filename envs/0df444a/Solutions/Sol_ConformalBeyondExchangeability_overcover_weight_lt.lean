-- Prove2me | solution 1 for ConformalBeyondExchangeability.overcover_weight_lt
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-24T21:04:33.754598+00:00
-- url     : https://prove2.me/submissions/73f7c32a-aa1b-4f34-af53-5a94c0037f6c

import Mathlib
import Definitions.Def_ConformalBeyondExchangeability_Basic

open MeasureTheory
namespace ConformalBeyondExchangeability

lemma ow_key {m : ℕ} (v : Fin m → ℝ) (r : Fin m → ℝ) {τ : ℝ} (hτ : 0 < τ) (k : Fin m)
    (hk : (r k : EReal) ≤ wQuantile v (fun i => (r i : EReal)) τ) :
    ∑ i, (if r i < r k then v i else 0) < τ := by
  classical
  by_contra h
  push_neg at h
  set F := Finset.univ.filter (fun i => r i < r k) with hF
  rcases F.eq_empty_or_nonempty with hFe | hFne
  · have : ∑ i, (if r i < r k then v i else 0) = 0 := by
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [if_neg]
      intro hi
      have : i ∈ F := by simp [hF, hi]
      rw [hFe] at this
      simp at this
    linarith
  obtain ⟨m0, hm0, hmax⟩ := Finset.exists_max_image F r hFne
  have hm0' : r m0 < r k := by simpa [hF] using hm0
  have hmem : (r m0 : EReal) ∈ {q : EReal | τ ≤ ∑ i, if (r i : EReal) ≤ q then v i else 0} := by
    simp only [Set.mem_setOf_eq]
    refine le_of_le_of_eq h (Finset.sum_congr rfl fun i _ => ?_)
    have : (r i : EReal) ≤ r m0 ↔ r i < r k := by
      rw [EReal.coe_le_coe_iff]
      constructor
      · intro hi; linarith
      · intro hi; exact hmax i (by simp [hF, hi])
    simp only [this]
  have hle : wQuantile v (fun i => (r i : EReal)) τ ≤ r m0 := sInf_le hmem
  have : (r k : EReal) ≤ r m0 := le_trans hk hle
  rw [EReal.coe_le_coe_iff] at this
  linarith

lemma ow_aux {n : ℕ} (a s : Fin n → ℝ) (P y α : ℝ) (c : Fin n → Prop) [DecidablePred c]
    (cx : Prop) [Decidable cx] (ha0 : ∀ j, 0 ≤ a j) (haP : ∀ j, a j ≤ P) (hP : 0 ≤ P)
    (hs : Function.Injective s) (hsy : ∀ j, s j ≠ y) (hα1 : α < 1)
    (hK : ∀ j, c j →
      ∑ i, (if s i < s j then a i else 0) + (if y < s j then a j else 0) < 1 - α)
    (hX : cx → ∑ i, (if s i < y then a i else 0) < 1 - α) :
    ∑ j, a j * (if c j then 1 else 0) + P * (if cx then 1 else 0) < 1 - α + P := by
  classical
  have hsum : ∑ j, a j * (if c j then 1 else 0) = ∑ j ∈ Finset.univ.filter c, a j := by
    rw [Finset.sum_filter]; refine Finset.sum_congr rfl fun j _ => ?_; split_ifs <;> simp
  rw [hsum]
  set K := Finset.univ.filter c with hKdef
  have hPx : P * (if cx then 1 else 0) ≤ P := by split_ifs <;> simp [hP]
  rcases K.eq_empty_or_nonempty with hKe | hKne
  · rw [hKe, Finset.sum_empty]; linarith
  obtain ⟨j0, hj0, hmax⟩ := Finset.exists_max_image K s hKne
  have hcj0 : c j0 := by simpa [hKdef] using hj0
  set H := ∑ i, (if s i < s j0 then a i else 0) with hH
  have hsub : ∑ j ∈ K, a j ≤ H + a j0 := by
    rw [← Finset.add_sum_erase K a hj0, add_comm]
    gcongr
    calc ∑ j ∈ K.erase j0, a j = ∑ j ∈ K.erase j0, (if s j < s j0 then a j else 0) := by
          refine Finset.sum_congr rfl fun j hj => ?_
          rw [if_pos]
          have hjK := Finset.mem_of_mem_erase hj
          have hne : j ≠ j0 := Finset.ne_of_mem_erase hj
          exact lt_of_le_of_ne (hmax j hjK) (fun h => hne (hs h))
      _ ≤ H := Finset.sum_le_univ_sum_of_nonneg (fun j => by split_ifs <;> simp [ha0])
  rcases lt_or_gt_of_ne (hsy j0) with hlt | hgt
  · -- s j0 < y
    have h1 := hK j0 hcj0
    rw [if_neg (not_lt.mpr hlt.le), add_zero] at h1
    by_cases hc : cx
    · have h2 := hX hc
      have hmono : H + a j0 ≤ ∑ i, (if s i < y then a i else 0) := by
        rw [hH, ← Finset.add_sum_erase _ _ (Finset.mem_univ j0),
          ← Finset.add_sum_erase _ _ (Finset.mem_univ j0), if_neg (lt_irrefl _), if_pos hlt,
          zero_add, add_comm]
        gcongr with i hi
        split_ifs with h3 h4 <;> try simp [ha0]
        exact absurd (lt_trans h3 hlt) h4
      rw [if_pos hc, mul_one]; linarith
    · rw [if_neg hc, mul_zero]; linarith [haP j0]
  · have h1 := hK j0 hcj0
    rw [if_pos hgt] at h1
    linarith

theorem overcover_weight_lt {n : ℕ} (w : Fin n → ℝ) (hw : ∀ i, 0 ≤ w i ∧ w i ≤ 1)
    {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (r : Fin (n + 1) → ℝ) (hr : Function.Injective r) :
    ∑ k, normWeights w k *
        (if (r k : EReal) ≤
            wQuantile (fun i => normWeights w (swapIdx k i)) (fun i => (r i : EReal)) (1 - α)
          then 1 else 0) <
      1 - α + normWeights w (Fin.last n) := by
  classical
  set p := normWeights w with hpdef
  have hD : 0 < ∑ j, w j + 1 := by
    have : 0 ≤ ∑ j, w j := Finset.sum_nonneg fun j _ => (hw j).1
    linarith
  have hpcs : ∀ j : Fin n, p j.castSucc = w j / (∑ j, w j + 1) := by
    intro j; simp [hpdef, normWeights]
  have hpl : p (Fin.last n) = 1 / (∑ j, w j + 1) := by simp [hpdef, normWeights]
  have hτ : (0:ℝ) < 1 - α := by linarith
  rw [Fin.sum_univ_castSucc]
  refine ow_aux (fun j => p j.castSucc) (fun j => r j.castSucc) (p (Fin.last n)) (r (Fin.last n)) α
    _ _ (fun j => ?_) (fun j => ?_) ?_ ?_ (fun j => ?_) hα1 (fun j hj => ?_) (fun hx => ?_)
  · rw [hpcs]; exact div_nonneg (hw j).1 hD.le
  · rw [hpcs, hpl]; exact div_le_div_of_nonneg_right (hw j).2 hD.le
  · rw [hpl]; positivity
  · intro i j h; exact Fin.castSucc_injective _ (hr h)
  · intro h; exact absurd (hr h) (Fin.castSucc_ne_last j)
  · have := ow_key _ r hτ _ hj
    rw [Fin.sum_univ_castSucc] at this
    convert this using 2
    · refine Finset.sum_congr rfl fun i _ => ?_
      by_cases hij : i = j
      · subst hij; simp
      · have : swapIdx j.castSucc i.castSucc = i.castSucc := by
          unfold swapIdx
          exact Equiv.swap_apply_of_ne_of_ne (fun h => hij (Fin.castSucc_injective _ h))
            (Fin.castSucc_ne_last i)
        simp only [this]
    · simp [swapIdx, Equiv.swap_apply_right]
  · have := ow_key _ r hτ _ hx
    rw [Fin.sum_univ_castSucc] at this
    simpa [swapIdx, Equiv.swap_self] using this

end ConformalBeyondExchangeability

open ConformalBeyondExchangeability in
theorem solution {n : ℕ} (w : Fin n → ℝ) (hw : ∀ i, 0 ≤ w i ∧ w i ≤ 1)
    {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (r : Fin (n + 1) → ℝ) (hr : Function.Injective r) :
    ∑ k, normWeights w k *
        (if (r k : EReal) ≤
            wQuantile (fun i => normWeights w (swapIdx k i)) (fun i => (r i : EReal)) (1 - α)
          then 1 else 0) <
      1 - α + normWeights w (Fin.last n) :=
  ConformalBeyondExchangeability.overcover_weight_lt w hw hα0 hα1 r hr
