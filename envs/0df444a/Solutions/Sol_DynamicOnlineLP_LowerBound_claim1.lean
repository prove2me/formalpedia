-- Prove2me | solution 1 for DynamicOnlineLP.LowerBound.claim1
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-29T04:59:33.232025+00:00
-- url     : https://prove2.me/submissions/85357884-cb88-4b76-a343-22ecedb91f65

import Mathlib.Tactic.Choose
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Data.Nat.Bitwise
import Definitions.Def_DynamicOnlineLP_LowerBound_OnlineLP
import Definitions.Def_DynamicOnlineLP_LowerBound_HardInstance
import Theorems.Thm_DynamicOnlineLP_LowerBound_hard_opt_le

open scoped BigOperators

namespace Claim1Proof

open DynamicOnlineLP.LowerBound

noncomputable def va {z k s : ℕ} {q : Fin z → ℕ} (x : HardCol z k s q → ℝ)
    (i : Fin z) : ℝ := ∑ j : Fin k, x ⟨i, Sum.inl j⟩

noncomputable def wa {z k s : ℕ} {q : Fin z → ℕ} (x : HardCol z k s q → ℝ)
    (i : Fin z) : ℝ := ∑ j : Fin (q i), x ⟨i, Sum.inr (Sum.inl j)⟩

noncomputable def wb {z k s : ℕ} {q : Fin z → ℕ} (x : HardCol z k s q → ℝ)
    (i : Fin z) : ℝ := ∑ j : Fin s, x ⟨i, Sum.inr (Sum.inr (Sum.inl j))⟩

noncomputable def wc {z k s : ℕ} {q : Fin z → ℕ} (x : HardCol z k s q → ℝ)
    (i : Fin z) : ℝ := ∑ j : Fin (2 * k - q i), x ⟨i, Sum.inr (Sum.inr (Sum.inr j))⟩

lemma accepted_eq {z k s : ℕ} {q : Fin z → ℕ} (x : HardCol z k s q → ℝ)
    (i : Fin z) : acceptedW x i = wa x i + wb x i + wc x i := by
  classical
  simp [acceptedW, wa, wb, wc, Fintype.sum_sigma, Fintype.sum_sum_type, add_assoc]

lemma objective_eq {z k s : ℕ} {q : Fin z → ℕ} (x : HardCol z k s q → ℝ) :
    objective (hardProfit z k s q) x =
      ∑ i : Fin z, (4 * va x i + 3 * wa x i + 2 * wb x i + wc x i) := by
  simp [objective, hardProfit, va, wa, wb, wc, Fintype.sum_sigma,
    Fintype.sum_sum_type, Finset.mul_sum, add_assoc]

lemma load_eq {z k s : ℕ} {q : Fin z → ℕ} (x : HardCol z k s q → ℝ)
    (j : Fin (2 ^ z)) :
    (∑ c : HardCol z k s q, hardDemand z k s q c j * x c) =
      ∑ i : Fin z, (vVec z i j * va x i + wVec z i j * (wa x i + wb x i + wc x i)) := by
  simp [hardDemand, va, wa, wb, wc, Fintype.sum_sigma, Fintype.sum_sum_type,
    Finset.mul_sum, mul_add, add_assoc]

lemma group_bounds {z k s : ℕ} {q : Fin z → ℕ} (x : HardCol z k s q → ℝ)
    (hx : ∀ c, 0 ≤ x c ∧ x c ≤ 1) (i : Fin z) :
    (0 ≤ va x i ∧ va x i ≤ k) ∧ (0 ≤ wa x i ∧ wa x i ≤ q i) ∧
    (0 ≤ wb x i ∧ wb x i ≤ s) ∧
      (0 ≤ wc x i ∧ wc x i ≤ ((2 * k - q i : ℕ) : ℝ)) := by
  have bound {n : ℕ} (f : Fin n → ℝ) (hf : ∀ j, 0 ≤ f j ∧ f j ≤ 1) :
      0 ≤ ∑ j, f j ∧ ∑ j, f j ≤ (n : ℝ) := by
    refine ⟨Finset.sum_nonneg (fun j _ ↦ (hf j).1), ?_⟩
    calc ∑ j, f j ≤ ∑ _j : Fin n, (1 : ℝ) :=
        Finset.sum_le_sum (fun j _ ↦ (hf j).2)
      _ = n := by simp
  exact ⟨bound _ (fun j ↦ hx _), bound _ (fun j ↦ hx _),
    bound _ (fun j ↦ hx _), bound _ (fun j ↦ hx _)⟩

lemma quota_dual (k q s l : ℝ) (hk : 0 ≤ k) (hq : 0 ≤ q) (hs : 0 ≤ s)
    (hl : 0 ≤ l) (hql : k ≤ q + l) :
    ∃ a b c t : ℝ,
      (0 ≤ a ∧ a ≤ q) ∧ (0 ≤ b ∧ b ≤ s) ∧ (0 ≤ c ∧ c ≤ l) ∧
      a + b + c = k ∧ 1 ≤ t ∧ t ≤ 3 ∧
      ∀ A B C : ℝ, (0 ≤ A ∧ A ≤ q) → (0 ≤ B ∧ B ≤ s) → (0 ≤ C ∧ C ≤ l) →
        3 * A + 2 * B + C ≤ 3 * a + 2 * b + c + t * (A + B + C - k) := by
  by_cases hqk : k ≤ q
  · refine ⟨k, 0, 0, 3, ⟨hk, hqk⟩, ⟨le_rfl, hs⟩, ⟨le_rfl, hl⟩,
      by ring, by norm_num, le_rfl, ?_⟩
    intro A B C hA hB hC
    linarith
  · by_cases hqs : k ≤ q + s
    · refine ⟨q, k - q, 0, 2, ⟨hq, le_rfl⟩, ⟨by linarith, by linarith⟩,
        ⟨le_rfl, hl⟩, by ring, by norm_num, by norm_num, ?_⟩
      intro A B C hA hB hC
      linarith
    · refine ⟨q, s, k - q - s, 1, ⟨hq, le_rfl⟩, ⟨hs, le_rfl⟩,
        ⟨by linarith, by linarith⟩, by ring, le_rfl, by norm_num, ?_⟩
      intro A B C hA hB hC
      linarith

lemma uniform_quota {n : ℕ} {a : ℝ} (ha : 0 ≤ a) (han : a ≤ n) :
    (∀ _i : Fin n, 0 ≤ a / n ∧ a / n ≤ 1) ∧ ∑ _i : Fin n, a / n = a := by
  by_cases hn : n = 0
  · subst n
    have han' : a ≤ 0 := by simpa using han
    have : a = 0 := le_antisymm han' ha
    simp [this]
  · have hn' : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
    constructor
    · intro i
      exact ⟨div_nonneg ha hn'.le, (div_le_one hn').2 han⟩
    · simp [ne_of_gt hn', mul_div_cancel₀]

lemma exists_bits {z : ℕ} (f : Fin z → Bool) :
    ∃ j : Fin (2 ^ z), ∀ i : Fin z, Nat.testBit j.val i.val = f i := by
  let bs := List.ofFn f
  let b := BitVec.ofBoolListLE bs
  have hlen : bs.length = z := List.length_ofFn
  refine ⟨⟨b.toNat, by simpa [hlen] using b.isLt⟩, ?_⟩
  intro i
  change b.toNat.testBit i.val = f i
  rw [BitVec.testBit_toNat]
  change (BitVec.ofBoolListLE (List.ofFn f)).getLsbD i.val = f i
  rw [BitVec.getLsbD_ofBoolListLE]
  simp [List.getD_eq_getElem?_getD, i.isLt]

lemma loss_le (v r k t : ℝ) (hv : v ≤ k) (ht : 1 ≤ t) (ht' : t ≤ 3) :
    t * (r - k) + |r - k| ≤ 4 * (max v r - v) := by
  rcases le_total k r with h | h
  · rw [abs_of_nonneg (by linarith)]
    have : max v r = r := max_eq_right (by linarith)
    rw [this]
    have hprod : (t - 3) * (r - k) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)
    nlinarith
  · rw [abs_of_nonpos (by linarith)]
    have := le_max_left v r
    have hprod : (t - 1) * (r - k) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)
    nlinarith

lemma max_sum_le {z k s : ℕ} {q : Fin z → ℕ} (x : HardCol z k s q → ℝ)
    (hx : IsFeasible (hardDemand z k s q) (hardCapacity z k) x) :
    ∑ i : Fin z, max (va x i) (acceptedW x i) ≤ (z : ℝ) * k := by
  classical
  obtain ⟨j, hj⟩ := exists_bits (fun i ↦ decide (acceptedW x i ≤ va x i))
  have heq : ∀ i : Fin z,
      vVec z i j * va x i + wVec z i j * (wa x i + wb x i + wc x i) =
        max (va x i) (acceptedW x i) := by
    intro i
    rw [← accepted_eq]
    by_cases h : acceptedW x i ≤ va x i
    · simp [vVec, wVec, hj, h]
    · simp [vVec, wVec, hj, h, max_eq_right (le_of_not_ge h)]
  have hcap := hx.1 j
  rw [load_eq] at hcap
  simpa only [heq, hardCapacity] using hcap

lemma objective_le_opt {ι : Type} [Fintype ι] {m : ℕ} (p : ι → ℝ)
    (a : ι → Fin m → ℝ) (b : Fin m → ℝ) (x : ι → ℝ) (hx : IsFeasible a b x) :
    objective p x ≤ OPT p a b := by
  classical
  apply le_csSup
  · refine ⟨∑ j, |p j|, ?_⟩
    rintro _ ⟨y, hy, rfl⟩
    apply Finset.sum_le_sum
    intro j hj
    have h := hy.2 j
    calc p j * y j ≤ |p j| * y j := mul_le_mul_of_nonneg_right (le_abs_self _) h.1
      _ ≤ |p j| * 1 := mul_le_mul_of_nonneg_left h.2 (abs_nonneg _)
      _ = |p j| := mul_one _
  · exact ⟨x, hx, rfl⟩

lemma objective_gap {z k s : ℕ} {q : Fin z → ℕ} (hq : ∀ i, q i ≤ 2 * k)
    (x : HardCol z k s q → ℝ)
    (hx : IsFeasible (hardDemand z k s q) (hardCapacity z k) x) :
    objective (hardProfit z k s q) x + ∑ i : Fin z, |acceptedW x i - (k : ℝ)| ≤
      OPT (hardProfit z k s q) (hardDemand z k s q) (hardCapacity z k) := by
  classical
  have hdata (i : Fin z) := quota_dual (k : ℝ) (q i : ℝ) (s : ℝ)
    ((2 * k - q i : ℕ) : ℝ) (Nat.cast_nonneg _) (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    (Nat.cast_nonneg _) (by
      rw [Nat.cast_sub (hq i)]
      push_cast
      have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg _
      linarith)
  choose a b c t h using hdata
  have ha (i : Fin z) := (h i).1
  have hb (i : Fin z) := (h i).2.1
  have hc (i : Fin z) := (h i).2.2.1
  have hs (i : Fin z) := (h i).2.2.2.1
  have ht (i : Fin z) := (h i).2.2.2.2.1
  have ht' (i : Fin z) := (h i).2.2.2.2.2.1
  have hd (i : Fin z) := (h i).2.2.2.2.2.2
  let y : HardCol z k s q → ℝ
    | ⟨_, Sum.inl _⟩ => 1
    | ⟨i, Sum.inr (Sum.inl _)⟩ => a i / (q i : ℝ)
    | ⟨i, Sum.inr (Sum.inr (Sum.inl _))⟩ => b i / (s : ℝ)
    | ⟨i, Sum.inr (Sum.inr (Sum.inr _))⟩ => c i / ((2 * k - q i : ℕ) : ℝ)
  have hya (i : Fin z) : va y i = k := by simp [va, y]
  have hyb (i : Fin z) : wa y i = a i := by
    simpa [wa, y] using (uniform_quota (ha i).1 (ha i).2).2
  have hyc (i : Fin z) : wb y i = b i := by
    simpa [wb, y] using (uniform_quota (hb i).1 (hb i).2).2
  have hyd (i : Fin z) : wc y i = c i := by
    simpa [wc, y] using (uniform_quota (hc i).1 (hc i).2).2
  have hy : IsFeasible (hardDemand z k s q) (hardCapacity z k) y := by
    constructor
    · intro j
      rw [load_eq]
      simp_rw [hya, hyb, hyc, hyd, hs]
      simp [wVec, hardCapacity, ← add_mul]
    · rintro ⟨i, u⟩
      rcases u with u | u | u | u
      · exact ⟨zero_le_one, le_rfl⟩
      · exact (uniform_quota (ha i).1 (ha i).2).1 u
      · exact (uniform_quota (hb i).1 (hb i).2).1 u
      · exact (uniform_quota (hc i).1 (hc i).2).1 u
  have hpoint (i : Fin z) :
      (4 * va x i + 3 * wa x i + 2 * wb x i + wc x i) + |acceptedW x i - (k : ℝ)| ≤
        4 * max (va x i) (acceptedW x i) + (3 * a i + 2 * b i + c i) := by
    obtain ⟨hv, hw, hw', hw''⟩ := group_bounds x hx.2 i
    have hdual := hd i (wa x i) (wb x i) (wc x i) hw hw' hw''
    have hloss := loss_le (va x i) (acceptedW x i) k (t i) hv.2 (ht i) (ht' i)
    rw [← accepted_eq] at hdual
    linarith
  have hobjy : objective (hardProfit z k s q) y =
      4 * ((z : ℝ) * k) + ∑ i : Fin z, (3 * a i + 2 * b i + c i) := by
    rw [objective_eq]
    simp_rw [hya, hyb, hyc, hyd]
    calc (∑ i : Fin z, (4 * (k : ℝ) + 3 * a i + 2 * b i + c i)) =
          ∑ i : Fin z, (4 * (k : ℝ) + (3 * a i + 2 * b i + c i)) := by
            apply Finset.sum_congr rfl
            intro i hi
            ring
      _ = _ := by rw [Finset.sum_add_distrib]; simp; ring
  calc objective (hardProfit z k s q) x + ∑ i : Fin z, |acceptedW x i - (k : ℝ)| =
        ∑ i : Fin z, ((4 * va x i + 3 * wa x i + 2 * wb x i + wc x i) +
          |acceptedW x i - (k : ℝ)|) := by simp only [objective_eq, Finset.sum_add_distrib]
    _ ≤ ∑ i : Fin z,
        (4 * max (va x i) (acceptedW x i) + (3 * a i + 2 * b i + c i)) :=
      Finset.sum_le_sum (fun i _ ↦ hpoint i)
    _ = 4 * (∑ i : Fin z, max (va x i) (acceptedW x i)) +
        ∑ i : Fin z, (3 * a i + 2 * b i + c i) := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum]
    _ ≤ 4 * ((z : ℝ) * k) + ∑ i : Fin z, (3 * a i + 2 * b i + c i) := by
      linarith [max_sum_le x hx]
    _ = objective (hardProfit z k s q) y := hobjy.symm
    _ ≤ _ := objective_le_opt _ _ _ y hy

lemma opt_lower (z k s : ℕ) (q : Fin z → ℕ) :
    4 * ((z : ℝ) * k) ≤ OPT (hardProfit z k s q) (hardDemand z k s q) (hardCapacity z k) := by
  classical
  let y : HardCol z k s q → ℝ := fun c ↦ if c.2.isLeft then 1 else 0
  have hva (i : Fin z) : va y i = k := by simp [va, y]
  have hwa (i : Fin z) : wa y i = 0 := by simp [wa, y]
  have hwb (i : Fin z) : wb y i = 0 := by simp [wb, y]
  have hwc (i : Fin z) : wc y i = 0 := by simp [wc, y]
  have hy : IsFeasible (hardDemand z k s q) (hardCapacity z k) y := by
    constructor
    · intro j
      rw [load_eq]
      simp_rw [hva, hwa, hwb, hwc]
      calc ∑ i : Fin z, (vVec z i j * k + wVec z i j * (0 + 0 + 0)) ≤
            ∑ _i : Fin z, (k : ℝ) := by
              apply Finset.sum_le_sum
              intro i hi
              simp only [add_zero, mul_zero]
              unfold vVec
              split_ifs <;> simp [Nat.cast_nonneg]
        _ = hardCapacity z k j := by simp [hardCapacity]
    · intro c
      simp only [y]
      split_ifs <;> norm_num
  have ho : objective (hardProfit z k s q) y = 4 * ((z : ℝ) * k) := by
    rw [objective_eq]
    simp [hva, hwa, hwb, hwc]
    ring
  rw [← ho]
  exact objective_le_opt _ _ _ y hy

end Claim1Proof

open DynamicOnlineLP.LowerBound in
theorem solution (z k s : ℕ) (hz : 1 ≤ z) (q : Fin z → ℕ) (hq : ∀ i, q i ≤ 2 * k) (ε : ℝ)
    (x : HardCol z k s q → ℝ) (hx : IsFeasible (hardDemand z k s q) (hardCapacity z k) x)
    (hcomp : (1 - ε) * OPT (hardProfit z k s q) (hardDemand z k s q) (hardCapacity z k) ≤
      objective (hardProfit z k s q) x) :
    ∑ i : Fin z, |acceptedW x i - (k : ℝ)| ≤ 7 * ε * ((z : ℝ) * (k : ℝ)) := by
  have hgap := Claim1Proof.objective_gap hq x hx
  have hlo := Claim1Proof.opt_lower z k s q
  have hB : (0 : ℝ) ≤ (z : ℝ) * k := by positivity
  have hD : 0 ≤ ∑ i : Fin z, |acceptedW x i - (k : ℝ)| :=
    Finset.sum_nonneg (fun _ _ ↦ abs_nonneg _)
  have hloss : ∑ i : Fin z, |acceptedW x i - (k : ℝ)| ≤
      ε * OPT (hardProfit z k s q) (hardDemand z k s q) (hardCapacity z k) := by
    nlinarith
  by_cases hε : 0 ≤ ε
  · have hup := hard_opt_le z k s hz q hq
    calc ∑ i : Fin z, |acceptedW x i - (k : ℝ)| ≤
          ε * OPT (hardProfit z k s q) (hardDemand z k s q) (hardCapacity z k) := hloss
      _ ≤ ε * (7 * ((z : ℝ) * k)) := mul_le_mul_of_nonneg_left hup hε
      _ = 7 * ε * ((z : ℝ) * k) := by ring
  · have hε' : ε < 0 := lt_of_not_ge hε
    have hOPT : OPT (hardProfit z k s q) (hardDemand z k s q) (hardCapacity z k) = 0 := by
      have hn : 0 ≤ OPT (hardProfit z k s q) (hardDemand z k s q) (hardCapacity z k) :=
        le_trans (mul_nonneg (by norm_num) hB) hlo
      apply le_antisymm _ hn
      apply le_of_not_gt
      intro hp
      have := mul_neg_of_neg_of_pos hε' hp
      linarith
    have hBzero : (z : ℝ) * (k : ℝ) = 0 := by rw [hOPT] at hlo; linarith
    simpa [hOPT, hBzero] using hloss
