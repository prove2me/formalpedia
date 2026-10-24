-- Prove2me | solution 1 for FosterQueues.MG1.mean_first_passage_linear
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-24T05:20:22.727408+00:00
-- url     : https://prove2.me/submissions/bf0a9569-2e4c-42a8-94bb-d99c066cce21

import Mathlib
import Definitions.Def_FosterQueues_MG1_Model

open scoped ENNReal
open QueueingFundamentals.Foundations

set_option autoImplicit false

namespace MFP07

variable (P : TransitionMatrix)

lemma p_le_one (i j : ℕ) : P.p i j ≤ 1 :=
  le_hasSum (P.row_sum i) j (fun k _ => P.nonneg i k)

lemma fp_two (n i j : ℕ) : P.firstPassage (n + 2) i j =
    ∑' l, if l = j then 0 else P.p i l * P.firstPassage (n + 1) l j := rfl

lemma fp_bound : ∀ n i j, 0 ≤ P.firstPassage n i j ∧ P.firstPassage n i j ≤ 1 := by
  intro n
  induction n with
  | zero => intro i j; simp [TransitionMatrix.firstPassage]
  | succ n ih =>
    intro i j
    cases n with
    | zero => exact ⟨P.nonneg i j, p_le_one P i j⟩
    | succ m =>
      rw [fp_two]
      have h0 : ∀ l, 0 ≤ (if l = j then 0 else P.p i l * P.firstPassage (m + 1) l j) := by
        intro l; split_ifs
        · exact le_rfl
        · exact mul_nonneg (P.nonneg i l) (ih l j).1
      have h1 : ∀ l, (if l = j then 0 else P.p i l * P.firstPassage (m + 1) l j) ≤ P.p i l := by
        intro l; split_ifs
        · exact P.nonneg i l
        · exact mul_le_of_le_one_right (P.nonneg i l) (ih l j).2
      have hs := Summable.of_nonneg_of_le h0 h1 (P.row_sum i).summable
      refine ⟨tsum_nonneg h0, ?_⟩
      calc _ ≤ ∑' l, P.p i l := hs.tsum_le_tsum h1 (P.row_sum i).summable
        _ = 1 := (P.row_sum i).tsum_eq

lemma fp_two_enn (n i j : ℕ) : ENNReal.ofReal (P.firstPassage (n + 2) i j) =
    ∑' l, if l = j then 0 else
      ENNReal.ofReal (P.p i l) * ENNReal.ofReal (P.firstPassage (n + 1) l j) := by
  have h0 : ∀ l, 0 ≤ (if l = j then 0 else P.p i l * P.firstPassage (n + 1) l j) := by
    intro l; split_ifs
    · exact le_rfl
    · exact mul_nonneg (P.nonneg i l) (fp_bound P (n + 1) l j).1
  have h1 : ∀ l, (if l = j then 0 else P.p i l * P.firstPassage (n + 1) l j) ≤ P.p i l := by
    intro l; split_ifs
    · exact P.nonneg i l
    · exact mul_le_of_le_one_right (P.nonneg i l) (fp_bound P (n + 1) l j).2
  have hs := Summable.of_nonneg_of_le h0 h1 (P.row_sum i).summable
  rw [fp_two, ENNReal.ofReal_tsum_of_nonneg h0 hs]
  congr 1; funext l
  split_ifs
  · simp
  · rw [ENNReal.ofReal_mul (P.nonneg _ _)]

lemma conv_weight (A B : ℕ → ℝ≥0∞) (w : ℕ → ℝ≥0∞) :
    ∑' n, w n * ∑ b ∈ Finset.range (n + 1), A b * B (n - b) =
      ∑' p : ℕ × ℕ, w (p.1 + p.2) * (A p.1 * B p.2) := by
  rw [← (Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd (A := ℕ)).tsum_eq
    (fun p : ℕ × ℕ => w (p.1 + p.2) * (A p.1 * B p.2)), ENNReal.tsum_sigma']
  congr 1; funext n
  rw [← Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => A i * B j), Finset.mul_sum]
  simp only [Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd_apply]
  rw [Finset.tsum_subtype (Finset.HasAntidiagonal.antidiagonal n)
    (fun p : ℕ × ℕ => w (p.1 + p.2) * (A p.1 * B p.2))]
  refine Finset.sum_congr rfl (fun p hp => ?_)
  rw [Finset.HasAntidiagonal.mem_antidiagonal.mp hp]

noncomputable def FF (i j : ℕ) : ℝ≥0∞ := ∑' n, ENNReal.ofReal (P.firstPassage n i j)

lemma fp_two_enn0 (n i : ℕ) : ENNReal.ofReal (P.firstPassage (n + 2) i 0) =
    ∑' j, ENNReal.ofReal (P.p i (j + 1)) * ENNReal.ofReal (P.firstPassage (n + 1) (j + 1) 0) := by
  rw [fp_two_enn, tsum_eq_zero_add' ENNReal.summable]
  simp

lemma FF_rec (i : ℕ) : FF P i 0 =
    ENNReal.ofReal (P.p i 0) + ∑' j, ENNReal.ofReal (P.p i (j + 1)) * FF P (j + 1) 0 := by
  have hsplit : ∑' n, ENNReal.ofReal (P.firstPassage n i 0) =
      ENNReal.ofReal (P.firstPassage 0 i 0) + (ENNReal.ofReal (P.firstPassage 1 i 0) +
        ∑' n, ENNReal.ofReal (P.firstPassage (n + 2) i 0)) := by
    rw [tsum_eq_zero_add' ENNReal.summable, tsum_eq_zero_add' ENNReal.summable]
  have hshift : ∀ l, ∑' n, ENNReal.ofReal (P.firstPassage n l 0) =
      ∑' n, ENNReal.ofReal (P.firstPassage (n + 1) l 0) := by
    intro l; rw [tsum_eq_zero_add' ENNReal.summable]; simp [TransitionMatrix.firstPassage]
  unfold FF
  rw [hsplit]
  simp only [hshift]
  have e0 : P.firstPassage 0 i 0 = 0 := rfl
  have e1 : P.firstPassage 1 i 0 = P.p i 0 := rfl
  rw [e0, e1, ENNReal.ofReal_zero, zero_add]
  congr 1
  simp_rw [fp_two_enn0, ← ENNReal.tsum_mul_left]
  rw [ENNReal.tsum_comm]

section MG1

variable {k : ℕ → ℝ} (hP : P.p = FosterQueues.MG1.mg1Matrix k)
include hP

lemma p_shift (a l s : ℕ) (ha : 1 ≤ a) : P.p (a + s) (l + s) = P.p a l := by
  rw [hP]; unfold FosterQueues.MG1.mg1Matrix
  have h1 : a + s ≠ 0 := by omega
  have h2 : a ≠ 0 := by omega
  simp only [h1, h2, if_false]
  by_cases h : a ≤ l + 1
  · have h3 : a + s ≤ l + s + 1 := by omega
    rw [if_pos h3, if_pos h]; congr 1; omega
  · have h3 : ¬ a + s ≤ l + s + 1 := by omega
    rw [if_neg h3, if_neg h]

lemma p_low (a l : ℕ) (h : l + 1 < a) : P.p a l = 0 := by
  rw [hP]; unfold FosterQueues.MG1.mg1Matrix
  have h1 : a ≠ 0 := by omega
  have h2 : ¬ a ≤ l + 1 := by omega
  simp only [h1, h2, if_false]

lemma p_zero (l : ℕ) : P.p 0 l = k l := by
  rw [hP]; unfold FosterQueues.MG1.mg1Matrix; simp

lemma fp_shift : ∀ n a j s, j < a → P.firstPassage n (a + s) (j + s) = P.firstPassage n a j := by
  intro n
  induction n with
  | zero => intro a j s _; rfl
  | succ n ih =>
    intro a j s hja
    cases n with
    | zero => exact p_shift P hP a j s (by omega)
    | succ m =>
      rw [fp_two, fp_two]
      have hsupp : Function.support (fun l => if l = j + s then 0 else
          P.p (a + s) l * P.firstPassage (m + 1) l (j + s)) ⊆ Set.range (fun x => x + s) := by
        intro l hl
        by_contra hr
        apply hl
        have hls : l < s := by
          by_contra h
          exact hr ⟨l - s, Nat.sub_add_cancel (by omega)⟩
        show (if l = j + s then 0 else P.p (a + s) l * P.firstPassage (m + 1) l (j + s)) = 0
        rw [if_neg (by omega), p_low P hP (a + s) l (by omega), zero_mul]
      rw [← (add_left_injective s).tsum_eq hsupp]
      congr 1; funext l
      by_cases hl : l = j
      · subst hl; simp
      · rw [if_neg (by omega), if_neg hl, p_shift P hP a l s (by omega)]
        by_cases hlj : j < l
        · rw [ih l j s hlj]
        · rw [p_low P hP a l (by omega), zero_mul, zero_mul]

lemma fp_down (n s : ℕ) : P.firstPassage n (s + 1) s = P.firstPassage n 1 0 := by
  have h := fp_shift P hP n 1 0 s (by norm_num)
  rw [add_comm 1 s, zero_add] at h
  exact h

lemma conv (m : ℕ) (hm : 0 < m) :
    ∀ n a, m < a → ENNReal.ofReal (P.firstPassage n a 0) =
      ∑ b ∈ Finset.range (n + 1), ENNReal.ofReal (P.firstPassage b a m) *
        ENNReal.ofReal (P.firstPassage (n - b) m 0) := by
  intro n
  induction n with
  | zero => intro a _; simp [TransitionMatrix.firstPassage]
  | succ n ih =>
    intro a hma
    cases n with
    | zero =>
      have hp : P.p a 0 = 0 := p_low P hP a 0 (by omega)
      simp [Finset.sum_range_succ, hp, TransitionMatrix.firstPassage]
    | succ n =>
      rw [Finset.sum_range_succ', Finset.sum_range_succ']
      have e0 : P.firstPassage 0 a m = 0 := rfl
      have e1 : P.firstPassage (0 + 1) a m = P.p a m := rfl
      rw [e0, e1, ENNReal.ofReal_zero, zero_mul, add_zero]
      simp only [Nat.add_sub_add_right, Nat.add_sub_cancel]
      rw [fp_two_enn, ENNReal.tsum_eq_add_tsum_ite m, if_neg (by omega), add_comm]
      congr 1
      simp_rw [fp_two_enn, ← ENNReal.tsum_mul_right]
      rw [← Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
      congr 1; funext l
      by_cases hlm : l = m
      · simp [hlm]
      · by_cases hl : m < l
        · rw [if_neg hlm, if_neg (by omega), ih l hl, Finset.sum_range_succ',
            show P.firstPassage 0 l m = 0 from rfl, ENNReal.ofReal_zero, zero_mul, add_zero,
            Finset.mul_sum]
          refine Finset.sum_congr rfl (fun b _ => ?_)
          rw [if_neg hlm, Nat.add_sub_add_right, mul_assoc]
        · have hp : P.p a l = 0 := p_low P hP a l (by omega)
          simp [hlm, hp]

lemma conv_gen (m : ℕ) (hm : 0 < m) (a : ℕ) (hma : m < a) (w : ℕ → ℝ≥0∞) :
    ∑' n, w n * ENNReal.ofReal (P.firstPassage n a 0) =
      ∑' i, ∑' j, w (i + j) * (ENNReal.ofReal (P.firstPassage i a m) *
        ENNReal.ofReal (P.firstPassage j m 0)) := by
  have h := fun n => conv P hP m hm n a hma
  simp_rw [h]
  have hw := conv_weight (fun b => ENNReal.ofReal (P.firstPassage b a m))
    (fun b => ENNReal.ofReal (P.firstPassage b m 0)) w
  beta_reduce at hw
  rw [hw, ENNReal.tsum_prod (f := fun i j => w (i + j) * (ENNReal.ofReal (P.firstPassage i a m) *
    ENNReal.ofReal (P.firstPassage j m 0)))]

lemma conv_FF (m : ℕ) (hm : 0 < m) (a : ℕ) (hma : m < a) :
    FF P a 0 = FF P a m * FF P m 0 := by
  have h := conv_gen P hP m hm a hma (fun _ => 1)
  simp only [one_mul] at h
  unfold FF
  rw [h, ← ENNReal.tsum_mul_right]
  congr 1; funext i
  rw [← ENNReal.tsum_mul_left]

lemma conv_mu (m : ℕ) (hm : 0 < m) (a : ℕ) (hma : m < a) :
    FosterQueues.MG1.meanFirstPassage P a 0 =
      FosterQueues.MG1.meanFirstPassage P a m * FF P m 0 +
        FF P a m * FosterQueues.MG1.meanFirstPassage P m 0 := by
  have h := conv_gen P hP m hm a hma (fun n => (n : ℝ≥0∞))
  beta_reduce at h
  have e : ∀ (i j : ℕ), ((i + j : ℕ) : ℝ≥0∞) * (ENNReal.ofReal (P.firstPassage i a m) *
      ENNReal.ofReal (P.firstPassage j m 0)) =
      ((i : ℝ≥0∞) * ENNReal.ofReal (P.firstPassage i a m)) * ENNReal.ofReal (P.firstPassage j m 0) +
      ENNReal.ofReal (P.firstPassage i a m) * ((j : ℝ≥0∞) * ENNReal.ofReal (P.firstPassage j m 0)) := by
    intro i j; push_cast; ring
  unfold FosterQueues.MG1.meanFirstPassage FF
  rw [h]
  simp_rw [e, ENNReal.tsum_add, ENNReal.tsum_mul_left, ENNReal.tsum_mul_right]

lemma FF_down (s : ℕ) : FF P (s + 1) s = FF P 1 0 := by
  unfold FF; simp_rw [fp_down P hP]

lemma mu_down (s : ℕ) : FosterQueues.MG1.meanFirstPassage P (s + 1) s =
    FosterQueues.MG1.meanFirstPassage P 1 0 := by
  unfold FosterQueues.MG1.meanFirstPassage; simp_rw [fp_down P hP]

lemma FF_pow (s : ℕ) : FF P (s + 1) 0 = FF P 1 0 ^ (s + 1) := by
  induction s with
  | zero => simp
  | succ s ih =>
    rw [conv_FF P hP (s + 1) (by omega) (s + 1 + 1) (by omega), FF_down P hP, ih, pow_succ' _ (s + 1)]

lemma x_eq_one (hk : ∀ i, 0 < k i) (hsum : HasSum k 1) (h0 : FF P 0 0 = 1) :
    FF P 1 0 = 1 := by
  set x := FF P 1 0 with hxdef
  set g : ℕ → ℝ≥0∞ := fun j => ENNReal.ofReal (k j) with hg
  set c : ℕ → ℝ≥0∞ := fun j => ENNReal.ofReal (k j) * x ^ j with hc
  have hgsum : ∑' j, g j = 1 := by
    rw [hg, ← ENNReal.ofReal_tsum_of_nonneg (fun i => (hk i).le) hsum.summable, hsum.tsum_eq,
      ENNReal.ofReal_one]
  have hcsum : ∑' j, c j = 1 := by
    rw [tsum_eq_zero_add' ENNReal.summable, ← h0, FF_rec P 0]
    simp only [hc, pow_zero, mul_one, p_zero P hP]
    congr 1
    refine tsum_congr (fun j => ?_)
    rw [FF_pow P hP j]
  have hg1 : g 1 ≠ 0 := (ENNReal.ofReal_pos.2 (hk 1)).ne'
  have hg1' : g 1 ≠ ⊤ := ENNReal.ofReal_ne_top
  rcases lt_trichotomy x 1 with hx | hx | hx
  · exfalso
    have hle : ∀ j, c j ≤ g j := fun j =>
      mul_le_of_le_one_right zero_le (pow_le_one₀ zero_le hx.le)
    have hlt : c 1 < g 1 := by
      show g 1 * x ^ 1 < g 1
      calc g 1 * x ^ 1 = x * g 1 := by rw [pow_one, mul_comm]
        _ < 1 * g 1 := ENNReal.mul_lt_mul_left hg1 hg1' hx
        _ = g 1 := one_mul _
    have := ENNReal.tsum_lt_tsum (by rw [hcsum]; exact ENNReal.one_ne_top) hle hlt
    rw [hcsum, hgsum] at this
    exact lt_irrefl _ this
  · exact hx
  · exfalso
    have hle : ∀ j, g j ≤ c j := fun j =>
      le_mul_of_one_le_right zero_le (one_le_pow₀ hx.le)
    have hlt : g 1 < c 1 := by
      show g 1 < g 1 * x ^ 1
      calc g 1 = 1 * g 1 := (one_mul _).symm
        _ < x * g 1 := ENNReal.mul_lt_mul_left hg1 hg1' hx
        _ = g 1 * x ^ 1 := by rw [pow_one, mul_comm]
    have := ENNReal.tsum_lt_tsum (by rw [hgsum]; exact ENNReal.one_ne_top) hle hlt
    rw [hcsum, hgsum] at this
    exact lt_irrefl _ this

end MG1

end MFP07

open QueueingFundamentals.Foundations FosterQueues.MG1 ENNReal in
theorem solution (k : ℕ → ℝ) (hk : ∀ i, 0 < k i) (hsum : HasSum k 1)
    (P : TransitionMatrix) (hP : P.p = mg1Matrix k) (herg : P.PositiveRecurrent) :
    (∀ i : ℕ, i ≠ 0 → meanFirstPassage P i (i - 1) = meanFirstPassage P 1 0) ∧
    (∀ i : ℕ, i ≠ 0 → meanFirstPassage P i 0 = (i : ℝ≥0∞) * meanFirstPassage P 1 0) := by
  constructor
  · intro i hi
    obtain ⟨s, rfl⟩ : ∃ s, i = s + 1 := ⟨i - 1, by omega⟩
    unfold meanFirstPassage
    simp only [Nat.add_sub_cancel, MFP07.fp_down P hP]
  · intro i hi
    obtain ⟨s, rfl⟩ : ∃ s, i = s + 1 := ⟨i - 1, by omega⟩
    have hx : MFP07.FF P 1 0 = 1 := MFP07.x_eq_one P hP hk hsum (herg 0).1
    have hF : ∀ s : ℕ, MFP07.FF P (s + 1) 0 = 1 := by
      intro s; rw [MFP07.FF_pow P hP, hx, one_pow]
    induction s with
    | zero => simp
    | succ s ih =>
      rw [MFP07.conv_mu P hP (s + 1) (by omega) (s + 1 + 1) (by omega), MFP07.mu_down P hP,
        MFP07.FF_down P hP, hx, hF s, ih (by omega)]
      push_cast
      ring
