-- Prove2me | solution 1 for FosterQueues.MG1.theorem3_first_passage_equations
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-24T04:13:39.706578+00:00
-- url     : https://prove2.me/submissions/b606b082-0df5-4cae-bc3f-c3163bc9b63a

import Mathlib
import Definitions.Def_FosterQueues_MG1_Model

open scoped ENNReal
open QueueingFundamentals.Foundations

set_option autoImplicit false

namespace FP51

variable (P : TransitionMatrix)

lemma p_le_one (i j : ℕ) : P.p i j ≤ 1 :=
  le_hasSum (P.row_sum i) j (fun k _ => P.nonneg i k)

lemma fp_zero (i : ℕ) : P.firstPassage 0 i 0 = 0 := rfl

lemma fp_one (i : ℕ) : P.firstPassage 1 i 0 = P.p i 0 := rfl

lemma fp_two (n i : ℕ) : P.firstPassage (n + 2) i 0 =
    ∑' k, if k = 0 then 0 else P.p i k * P.firstPassage (n + 1) k 0 := rfl

lemma fp_bound : ∀ n i, 0 ≤ P.firstPassage n i 0 ∧ P.firstPassage n i 0 ≤ 1 := by
  intro n
  induction n with
  | zero => intro i; simp [fp_zero]
  | succ n ih =>
    intro i
    cases n with
    | zero => rw [fp_one]; exact ⟨P.nonneg i 0, p_le_one P i 0⟩
    | succ m =>
      show 0 ≤ P.firstPassage (m + 2) i 0 ∧ P.firstPassage (m + 2) i 0 ≤ 1
      rw [fp_two]
      have h0 : ∀ k, 0 ≤ (if k = 0 then 0 else P.p i k * P.firstPassage (m + 1) k 0) := by
        intro k; split_ifs
        · exact le_rfl
        · exact mul_nonneg (P.nonneg i k) (ih k).1
      have h1 : ∀ k, (if k = 0 then 0 else P.p i k * P.firstPassage (m + 1) k 0) ≤ P.p i k := by
        intro k; split_ifs
        · exact P.nonneg i k
        · exact mul_le_of_le_one_right (P.nonneg i k) (ih k).2
      have hs : Summable (fun k => if k = 0 then 0 else P.p i k * P.firstPassage (m + 1) k 0) :=
        Summable.of_nonneg_of_le h0 h1 (P.row_sum i).summable
      refine ⟨tsum_nonneg h0, ?_⟩
      calc _ ≤ ∑' k, P.p i k := hs.tsum_le_tsum h1 (P.row_sum i).summable
        _ = 1 := (P.row_sum i).tsum_eq

lemma fp_two_enn (n i : ℕ) : ENNReal.ofReal (P.firstPassage (n + 2) i 0) =
    ∑' j, ENNReal.ofReal (P.p i (j + 1)) * ENNReal.ofReal (P.firstPassage (n + 1) (j + 1) 0) := by
  have h0 : ∀ k, 0 ≤ (if k = 0 then 0 else P.p i k * P.firstPassage (n + 1) k 0) := by
    intro k; split_ifs
    · exact le_rfl
    · exact mul_nonneg (P.nonneg i k) (fp_bound P (n + 1) k).1
  have h1 : ∀ k, (if k = 0 then 0 else P.p i k * P.firstPassage (n + 1) k 0) ≤ P.p i k := by
    intro k; split_ifs
    · exact P.nonneg i k
    · exact mul_le_of_le_one_right (P.nonneg i k) (fp_bound P (n + 1) k).2
  have hs : Summable (fun k => if k = 0 then 0 else P.p i k * P.firstPassage (n + 1) k 0) :=
    Summable.of_nonneg_of_le h0 h1 (P.row_sum i).summable
  rw [fp_two, ENNReal.ofReal_tsum_of_nonneg h0 hs, tsum_eq_zero_add' ENNReal.summable]
  simp only [if_true, ENNReal.ofReal_zero, zero_add, Nat.add_one_ne_zero, if_false]
  congr 1
  funext j
  rw [ENNReal.ofReal_mul (P.nonneg _ _)]

/-- first-step decomposition with an arbitrary weight. -/
lemma first_step (w : ℕ → ℝ≥0∞) (i : ℕ) :
    ∑' n, w n * ENNReal.ofReal (P.firstPassage n i 0) =
      w 1 * ENNReal.ofReal (P.p i 0) +
      ∑' j, ENNReal.ofReal (P.p i (j + 1)) *
        ∑' n, w (n + 2) * ENNReal.ofReal (P.firstPassage (n + 1) (j + 1) 0) := by
  have hsplit : ∑' n, w n * ENNReal.ofReal (P.firstPassage n i 0) =
      w 0 * ENNReal.ofReal (P.firstPassage 0 i 0) + (w 1 * ENNReal.ofReal (P.firstPassage 1 i 0)
        + ∑' n, w (n + 2) * ENNReal.ofReal (P.firstPassage (n + 2) i 0)) := by
    rw [tsum_eq_zero_add' ENNReal.summable, tsum_eq_zero_add' ENNReal.summable]
  rw [hsplit, fp_zero, fp_one, ENNReal.ofReal_zero, mul_zero, zero_add]
  congr 1
  simp_rw [fp_two_enn, ← ENNReal.tsum_mul_left]
  rw [ENNReal.tsum_comm]
  congr 1
  funext j
  congr 1
  funext n
  ring

noncomputable def FF (i : ℕ) : ℝ≥0∞ := ∑' n, ENNReal.ofReal (P.firstPassage n i 0)

lemma FF_shift (i : ℕ) : FF P i = ∑' n, ENNReal.ofReal (P.firstPassage (n + 1) i 0) := by
  unfold FF
  rw [tsum_eq_zero_add' ENNReal.summable, fp_zero, ENNReal.ofReal_zero, zero_add]

lemma mu_shift (i : ℕ) : FosterQueues.MG1.meanFirstPassage P i 0 =
    ∑' n, ((n + 1 : ℕ) : ℝ≥0∞) * ENNReal.ofReal (P.firstPassage (n + 1) i 0) := by
  unfold FosterQueues.MG1.meanFirstPassage
  rw [tsum_eq_zero_add' ENNReal.summable, fp_zero, ENNReal.ofReal_zero, mul_zero, zero_add]

lemma FF_rec (i : ℕ) : FF P i =
    ENNReal.ofReal (P.p i 0) + ∑' j, ENNReal.ofReal (P.p i (j + 1)) * FF P (j + 1) := by
  have h := first_step P (fun _ => 1) i
  simp only [one_mul] at h
  rw [FF, h]
  simp_rw [← FF_shift]

lemma mu_rec (i : ℕ) : FosterQueues.MG1.meanFirstPassage P i 0 =
    FF P i + ∑' j, ENNReal.ofReal (P.p i (j + 1)) * FosterQueues.MG1.meanFirstPassage P (j + 1) 0 := by
  have h := first_step P (fun n => (n : ℝ≥0∞)) i
  have hin : ∀ k, ∑' n, ((n + 2 : ℕ) : ℝ≥0∞) * ENNReal.ofReal (P.firstPassage (n + 1) k 0) =
      FosterQueues.MG1.meanFirstPassage P k 0 + FF P k := by
    intro k
    rw [mu_shift, FF_shift, ← ENNReal.tsum_add]
    congr 1
    funext n
    push_cast
    ring
  rw [Nat.cast_one, one_mul] at h
  unfold FosterQueues.MG1.meanFirstPassage at hin ⊢
  rw [h]
  simp_rw [hin, mul_add, ENNReal.tsum_add]
  rw [FF_rec P i, add_assoc]
  congr 1
  rw [add_comm]

lemma row_enn (i : ℕ) : ENNReal.ofReal (P.p i 0) + ∑' j, ENNReal.ofReal (P.p i (j + 1)) = 1 := by
  have h := tsum_eq_zero_add' (f := fun k => ENNReal.ofReal (P.p i k)) ENNReal.summable
  rw [← h, ← ENNReal.ofReal_tsum_of_nonneg (P.nonneg i) (P.row_sum i).summable,
    (P.row_sum i).tsum_eq, ENNReal.ofReal_one]

lemma G_le (N : ℕ) : ∀ i, ∑ n ∈ Finset.range N, ENNReal.ofReal (P.firstPassage (n + 1) i 0) ≤ 1 := by
  induction N with
  | zero => intro i; simp
  | succ N ih =>
    intro i
    rw [Finset.sum_range_succ']
    have e : ∀ n : ℕ, n + 1 + 1 = n + 2 := fun _ => rfl
    simp only [e, fp_two_enn, zero_add, fp_one]
    rw [← Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
    simp_rw [← Finset.mul_sum]
    calc _ ≤ ∑' j, ENNReal.ofReal (P.p i (j + 1)) + ENNReal.ofReal (P.p i 0) := by
          gcongr with j
          exact mul_le_of_le_one_right' (ih (j + 1))
      _ = 1 := by rw [add_comm, row_enn]

lemma FF_le_one (i : ℕ) : FF P i ≤ 1 := by
  rw [FF_shift, ENNReal.tsum_eq_iSup_nat]
  exact iSup_le fun N => G_le P N i

lemma spread_F (i j : ℕ) (hi : FF P i = 1) (hp : 0 < P.p i (j + 1)) : FF P (j + 1) = 1 := by
  by_contra hne
  have hlt : FF P (j + 1) < 1 := lt_of_le_of_ne (FF_le_one P _) hne
  have hfin : ∑' k, ENNReal.ofReal (P.p i (k + 1)) ≠ ⊤ := by
    intro h
    have := row_enn P i
    rw [h] at this
    simp at this
  have hlt2 : ∑' k, ENNReal.ofReal (P.p i (k + 1)) * FF P (k + 1) <
      ∑' k, ENNReal.ofReal (P.p i (k + 1)) := by
    refine ENNReal.tsum_lt_tsum (i := j)
      (ne_top_of_le_ne_top hfin (ENNReal.tsum_le_tsum fun k => ?_)) (fun k => ?_) ?_
    · exact mul_le_of_le_one_right' (FF_le_one P (k + 1))
    · exact mul_le_of_le_one_right' (FF_le_one P (k + 1))
    · have h0 : ENNReal.ofReal (P.p i (j + 1)) ≠ 0 := by simpa using hp
      calc _ < ENNReal.ofReal (P.p i (j + 1)) * 1 :=
            (ENNReal.mul_lt_mul_iff_right h0 ENNReal.ofReal_ne_top).2 hlt
        _ = _ := mul_one _
  have h3 : ENNReal.ofReal (P.p i 0) + ∑' k, ENNReal.ofReal (P.p i (k + 1)) * FF P (k + 1) < 1 := by
    rw [← row_enn P i]
    exact ENNReal.add_lt_add_left ENNReal.ofReal_ne_top hlt2
  rw [← FF_rec, hi] at h3
  exact lt_irrefl _ h3

lemma reach_F (h0 : FF P 0 = 1) :
    ∀ n i j, FF P i = 1 → 0 < P.stepProb n i j → FF P j = 1 := by
  intro n
  induction n with
  | zero =>
    intro i j hi hs
    change 0 < (if i = j then (1 : ℝ) else 0) at hs
    split_ifs at hs with h
    · subst h; exact hi
    · exact absurd hs (lt_irrefl 0)
  | succ n ih =>
    intro i j hi hs
    change 0 < ∑' k, P.p i k * P.stepProb n k j at hs
    obtain ⟨k, hk⟩ : ∃ k, 0 < P.p i k * P.stepProb n k j := by
      by_contra hc
      push Not at hc
      exact absurd (tsum_nonpos hc) (not_le.2 hs)
    have hboth := (pos_and_pos_or_neg_and_neg_of_mul_pos hk).resolve_right
      (fun h => absurd h.1 (not_lt.2 (P.nonneg i k)))
    apply ih k j _ hboth.2
    cases k with
    | zero => exact h0
    | succ k => exact spread_F P i k hi hboth.1

lemma spread_mu (i k : ℕ) (hi : FosterQueues.MG1.meanFirstPassage P i 0 < ⊤)
    (hp : 0 < P.p i (k + 1)) : FosterQueues.MG1.meanFirstPassage P (k + 1) 0 < ⊤ := by
  have hle : ENNReal.ofReal (P.p i (k + 1)) * FosterQueues.MG1.meanFirstPassage P (k + 1) 0 ≤
      FosterQueues.MG1.meanFirstPassage P i 0 := by
    rw [mu_rec P i]
    exact le_add_left (ENNReal.le_tsum (f := fun j =>
      ENNReal.ofReal (P.p i (j + 1)) * FosterQueues.MG1.meanFirstPassage P (j + 1) 0) k)
  by_contra htop
  rw [not_lt, top_le_iff] at htop
  have h0 : ENNReal.ofReal (P.p i (k + 1)) ≠ 0 := by simpa using hp
  rw [htop, ENNReal.mul_top h0] at hle
  exact absurd (top_le_iff.1 hle) (ne_of_lt hi)

lemma reach_mu (h0 : FosterQueues.MG1.meanFirstPassage P 0 0 < ⊤) :
    ∀ n i j, FosterQueues.MG1.meanFirstPassage P i 0 < ⊤ → 0 < P.stepProb n i j →
      FosterQueues.MG1.meanFirstPassage P j 0 < ⊤ := by
  intro n
  induction n with
  | zero =>
    intro i j hi hs
    change 0 < (if i = j then (1 : ℝ) else 0) at hs
    split_ifs at hs with h
    · subst h; exact hi
    · exact absurd hs (lt_irrefl 0)
  | succ n ih =>
    intro i j hi hs
    change 0 < ∑' k, P.p i k * P.stepProb n k j at hs
    obtain ⟨k, hk⟩ : ∃ k, 0 < P.p i k * P.stepProb n k j := by
      by_contra hc
      push Not at hc
      exact absurd (tsum_nonpos hc) (not_le.2 hs)
    have hboth := (pos_and_pos_or_neg_and_neg_of_mul_pos hk).resolve_right
      (fun h => absurd h.1 (not_lt.2 (P.nonneg i k)))
    apply ih k j _ hboth.2
    cases k with
    | zero => exact h0
    | succ k => exact spread_mu P i k hi hboth.1

end FP51

open QueueingFundamentals.Foundations FosterQueues.MG1 in
theorem solution (P : TransitionMatrix) (hirr : P.Irreducible)
    (hap : P.Aperiodic) (herg : P.PositiveRecurrent) :
    (∀ j : ℕ, j ≠ 0 → meanFirstPassage P j 0 < ⊤) ∧
    (∀ i : ℕ, i ≠ 0 → meanFirstPassage P i 0 =
      1 + ∑' j : ℕ, ENNReal.ofReal (P.p i (j + 1)) * meanFirstPassage P (j + 1) 0) ∧
    (∑' j : ℕ, ENNReal.ofReal (P.p 0 (j + 1)) * meanFirstPassage P (j + 1) 0) < ⊤ := by
  have hF0 : FP51.FF P 0 = 1 := (herg 0).1
  have hm0 : meanFirstPassage P 0 0 < ⊤ := (herg 0).2
  have hF : ∀ j, FP51.FF P j = 1 := fun j => by
    obtain ⟨n, hn⟩ := hirr 0 j
    exact FP51.reach_F P hF0 n 0 j hF0 hn
  have hrec : ∀ i, meanFirstPassage P i 0 =
      1 + ∑' j : ℕ, ENNReal.ofReal (P.p i (j + 1)) * meanFirstPassage P (j + 1) 0 := fun i => by
    rw [FP51.mu_rec, hF]
  refine ⟨fun j _ => ?_, fun i _ => hrec i, ?_⟩
  · obtain ⟨n, hn⟩ := hirr 0 j
    exact FP51.reach_mu P hm0 n 0 j hm0 hn
  · exact lt_of_le_of_lt (by rw [hrec 0]; exact le_add_self) hm0
