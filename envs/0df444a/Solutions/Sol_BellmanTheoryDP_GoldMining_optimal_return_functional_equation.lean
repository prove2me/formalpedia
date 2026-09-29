-- Prove2me | solution 1 for BellmanTheoryDP.GoldMining.optimal_return_functional_equation
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-28T14:41:14.396526+00:00
-- url     : https://prove2.me/submissions/a50b12d8-35f3-4fd3-b022-bb4075743414

import Mathlib
import Definitions.Def_BellmanTheoryDP_GoldMining_Model



namespace BellmanTheoryDP.GoldMining

/-- shift a choice sequence -/
def shift (σ : ChoiceSeq) : ChoiceSeq := fun n => σ (n + 1)

/-- prepend a choice -/
def cons (m : Mine) (τ : ChoiceSeq) : ChoiceSeq := fun n => Nat.casesOn n m τ

lemma shift_cons (m : Mine) (τ : ChoiceSeq) : shift (cons m τ) = τ := rfl

section

variable {p q r s : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (hq0 : 0 < q) (hq1 : q < 1)
  (hr0 : 0 < r) (hr1 : r < 1) (hs0 : 0 < s) (hs1 : s < 1)
include hp0 hp1 hq0 hq1 hr0 hr1 hs0 hs1

lemma succ_nonneg (m : Mine) : 0 ≤ successProb p q m := by
  cases m <;> simp [successProb] <;> linarith

lemma succ_le (m : Mine) : successProb p q m ≤ max p q := by
  cases m <;> simp [successProb]

lemma survival_nonneg (σ : ChoiceSeq) (n : ℕ) : 0 ≤ survival p q σ n :=
  Finset.prod_nonneg fun k _ =>
    succ_nonneg hp0 hp1 hq0 hq1 hr0 hr1 hs0 hs1 (σ k)

lemma survival_le (σ : ChoiceSeq) (n : ℕ) : survival p q σ n ≤ max p q ^ (n + 1) := by
  unfold survival
  calc ∏ k ∈ Finset.range (n + 1), successProb p q (σ k)
      ≤ ∏ _k ∈ Finset.range (n + 1), max p q :=
        Finset.prod_le_prod (fun k _ => succ_nonneg hp0 hp1 hq0 hq1 hr0 hr1 hs0 hs1 _)
          (fun k _ => succ_le hp0 hp1 hq0 hq1 hr0 hr1 hs0 hs1 _)
    _ = max p q ^ (n + 1) := by simp

lemma gain_nonneg (σ : ChoiceSeq) {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (n : ℕ) :
    0 ≤ gain r s σ x y n := by
  unfold gain
  cases σ n
  · simp only; exact mul_nonneg (mul_nonneg hr0.le hx) (pow_nonneg (by linarith) _)
  · simp only; exact mul_nonneg (mul_nonneg hs0.le hy) (pow_nonneg (by linarith) _)

lemma gain_le (σ : ChoiceSeq) {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (n : ℕ) :
    gain r s σ x y n ≤ r * x + s * y := by
  have hrx : 0 ≤ r * x := mul_nonneg hr0.le hx
  have hsy : 0 ≤ s * y := mul_nonneg hs0.le hy
  unfold gain
  cases σ n
  · simp only
    have : (1 - r) ^ usesA σ n ≤ 1 := pow_le_one₀ (by linarith) (by linarith)
    nlinarith
  · simp only
    have : (1 - s) ^ usesB σ n ≤ 1 := pow_le_one₀ (by linarith) (by linarith)
    nlinarith

lemma summable_ret (σ : ChoiceSeq) {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    Summable (fun n => survival p q σ n * gain r s σ x y n) := by
  have hK0 : 0 ≤ max p q := le_max_of_le_left hp0.le
  have hK1 : max p q < 1 := max_lt hp1 hq1
  refine Summable.of_nonneg_of_le
    (fun n => mul_nonneg (survival_nonneg hp0 hp1 hq0 hq1 hr0 hr1 hs0 hs1 σ n)
      (gain_nonneg hp0 hp1 hq0 hq1 hr0 hr1 hs0 hs1 σ hx hy n))
    (fun n => ?_) ((summable_geometric_of_lt_one hK0 hK1).mul_left ((r * x + s * y) * max p q))
  calc survival p q σ n * gain r s σ x y n ≤ max p q ^ (n + 1) * (r * x + s * y) :=
        mul_le_mul (survival_le hp0 hp1 hq0 hq1 hr0 hr1 hs0 hs1 σ n)
          (gain_le hp0 hp1 hq0 hq1 hr0 hr1 hs0 hs1 σ hx hy n)
          (gain_nonneg hp0 hp1 hq0 hq1 hr0 hr1 hs0 hs1 σ hx hy n) (pow_nonneg hK0 _)
    _ = (r * x + s * y) * max p q * max p q ^ n := by ring

lemma ret_nonneg (σ : ChoiceSeq) {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    0 ≤ expectedReturn p q r s σ x y :=
  tsum_nonneg fun n => mul_nonneg (survival_nonneg hp0 hp1 hq0 hq1 hr0 hr1 hs0 hs1 σ n)
    (gain_nonneg hp0 hp1 hq0 hq1 hr0 hr1 hs0 hs1 σ hx hy n)

lemma ret_le (σ : ChoiceSeq) {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    expectedReturn p q r s σ x y ≤ (r * x + s * y) * max p q / (1 - max p q) := by
  have hK0 : 0 ≤ max p q := le_max_of_le_left hp0.le
  have hK1 : max p q < 1 := max_lt hp1 hq1
  have hg := (summable_geometric_of_lt_one hK0 hK1).mul_left ((r * x + s * y) * max p q)
  unfold expectedReturn
  calc ∑' n, survival p q σ n * gain r s σ x y n
      ≤ ∑' n, (r * x + s * y) * max p q * max p q ^ n := by
        refine (summable_ret hp0 hp1 hq0 hq1 hr0 hr1 hs0 hs1 σ hx hy).tsum_le_tsum (fun n => ?_) hg
        calc survival p q σ n * gain r s σ x y n ≤ max p q ^ (n + 1) * (r * x + s * y) :=
              mul_le_mul (survival_le hp0 hp1 hq0 hq1 hr0 hr1 hs0 hs1 σ n)
                (gain_le hp0 hp1 hq0 hq1 hr0 hr1 hs0 hs1 σ hx hy n)
                (gain_nonneg hp0 hp1 hq0 hq1 hr0 hr1 hs0 hs1 σ hx hy n) (pow_nonneg hK0 _)
          _ = (r * x + s * y) * max p q * max p q ^ n := by ring
    _ = (r * x + s * y) * max p q / (1 - max p q) := by
        rw [tsum_mul_left, tsum_geometric_of_lt_one hK0 hK1]; ring

end

lemma usesA_succ_A (σ : ChoiceSeq) (h : σ 0 = Mine.A) (n : ℕ) :
    usesA σ (n + 1) = usesA (shift σ) n + 1 := by
  unfold usesA
  rw [Finset.card_filter, Finset.card_filter, Finset.sum_range_succ']
  simp [h, shift, -Finset.sum_boole]
  exact Finset.sum_congr rfl fun k _ => by congr

lemma usesB_succ_A (σ : ChoiceSeq) (h : σ 0 = Mine.A) (n : ℕ) :
    usesB σ (n + 1) = usesB (shift σ) n := by
  unfold usesB
  rw [Finset.card_filter, Finset.card_filter, Finset.sum_range_succ']
  simp [h, shift, -Finset.sum_boole]
  exact Finset.sum_congr rfl fun k _ => by congr

lemma usesA_succ_B (σ : ChoiceSeq) (h : σ 0 = Mine.B) (n : ℕ) :
    usesA σ (n + 1) = usesA (shift σ) n := by
  unfold usesA
  rw [Finset.card_filter, Finset.card_filter, Finset.sum_range_succ']
  simp [h, shift, -Finset.sum_boole]
  exact Finset.sum_congr rfl fun k _ => by congr

lemma usesB_succ_B (σ : ChoiceSeq) (h : σ 0 = Mine.B) (n : ℕ) :
    usesB σ (n + 1) = usesB (shift σ) n + 1 := by
  unfold usesB
  rw [Finset.card_filter, Finset.card_filter, Finset.sum_range_succ']
  simp [h, shift, -Finset.sum_boole]
  exact Finset.sum_congr rfl fun k _ => by congr

lemma survival_succ (p q : ℝ) (σ : ChoiceSeq) (n : ℕ) :
    survival p q σ (n + 1) = successProb p q (σ 0) * survival p q (shift σ) n := by
  unfold survival
  rw [Finset.prod_range_succ' _ (n + 1)]
  simp [shift, mul_comm]

lemma gain_succ_A (r s : ℝ) (σ : ChoiceSeq) (h : σ 0 = Mine.A) (x y : ℝ) (n : ℕ) :
    gain r s σ x y (n + 1) = gain r s (shift σ) ((1 - r) * x) y n := by
  unfold gain
  have e : σ (n + 1) = shift σ n := rfl
  rw [e]
  cases hσ : shift σ n
  · simp only; rw [usesA_succ_A σ h, pow_succ]; ring
  · simp only; rw [usesB_succ_A σ h]

lemma gain_succ_B (r s : ℝ) (σ : ChoiceSeq) (h : σ 0 = Mine.B) (x y : ℝ) (n : ℕ) :
    gain r s σ x y (n + 1) = gain r s (shift σ) x ((1 - s) * y) n := by
  unfold gain
  have e : σ (n + 1) = shift σ n := rfl
  rw [e]
  cases hσ : shift σ n
  · simp only; rw [usesA_succ_B σ h]
  · simp only; rw [usesB_succ_B σ h, pow_succ]; ring


section Main

variable {p q r s : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (hq0 : 0 < q) (hq1 : q < 1)
  (hr0 : 0 < r) (hr1 : r < 1) (hs0 : 0 < s) (hs1 : s < 1)
include hp0 hp1 hq0 hq1 hr0 hr1 hs0 hs1

lemma ret_A (σ : ChoiceSeq) (h : σ 0 = Mine.A) {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    expectedReturn p q r s σ x y =
      p * (r * x + expectedReturn p q r s (shift σ) ((1 - r) * x) y) := by
  unfold expectedReturn
  rw [(summable_ret hp0 hp1 hq0 hq1 hr0 hr1 hs0 hs1 σ hx hy).tsum_eq_zero_add]
  have e0 : survival p q σ 0 * gain r s σ x y 0 = p * (r * x) := by
    simp [survival, gain, h, successProb, usesA]
  have e1 : ∀ n, survival p q σ (n + 1) * gain r s σ x y (n + 1) =
      p * (survival p q (shift σ) n * gain r s (shift σ) ((1 - r) * x) y n) := fun n => by
    rw [survival_succ, gain_succ_A r s σ h, h]; simp only [successProb]; ring
  rw [e0, tsum_congr e1, tsum_mul_left]; ring

lemma ret_B (σ : ChoiceSeq) (h : σ 0 = Mine.B) {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    expectedReturn p q r s σ x y =
      q * (s * y + expectedReturn p q r s (shift σ) x ((1 - s) * y)) := by
  unfold expectedReturn
  rw [(summable_ret hp0 hp1 hq0 hq1 hr0 hr1 hs0 hs1 σ hx hy).tsum_eq_zero_add]
  have e0 : survival p q σ 0 * gain r s σ x y 0 = q * (s * y) := by
    simp [survival, gain, h, successProb, usesB]
  have e1 : ∀ n, survival p q σ (n + 1) * gain r s σ x y (n + 1) =
      q * (survival p q (shift σ) n * gain r s (shift σ) x ((1 - s) * y) n) := fun n => by
    rw [survival_succ, gain_succ_B r s σ h, h]; simp only [successProb]; ring
  rw [e0, tsum_congr e1, tsum_mul_left]; ring

lemma bdd_ret {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    BddAbove (Set.range fun σ => expectedReturn p q r s σ x y) :=
  ⟨_, by rintro _ ⟨σ, rfl⟩; exact ret_le hp0 hp1 hq0 hq1 hr0 hr1 hs0 hs1 σ hx hy⟩

theorem functional_eq_main (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    optimalReturn p q r s x y =
      max (p * (r * x + optimalReturn p q r s ((1 - r) * x) y))
          (q * (s * y + optimalReturn p q r s x ((1 - s) * y))) := by
  haveI : Nonempty ChoiceSeq := ⟨fun _ => Mine.A⟩
  have hx' : 0 ≤ (1 - r) * x := mul_nonneg (by linarith) hx
  have hy' : 0 ≤ (1 - s) * y := mul_nonneg (by linarith) hy
  have B0 := bdd_ret hp0 hp1 hq0 hq1 hr0 hr1 hs0 hs1 hx hy
  have BA := bdd_ret hp0 hp1 hq0 hq1 hr0 hr1 hs0 hs1 hx' hy
  have BB := bdd_ret hp0 hp1 hq0 hq1 hr0 hr1 hs0 hs1 hx hy'
  unfold optimalReturn
  apply le_antisymm
  · refine ciSup_le fun σ => ?_
    cases h : σ 0
    · rw [ret_A hp0 hp1 hq0 hq1 hr0 hr1 hs0 hs1 σ h hx hy]
      exact le_max_of_le_left (mul_le_mul_of_nonneg_left
        (add_le_add le_rfl (le_ciSup BA (shift σ))) hp0.le)
    · rw [ret_B hp0 hp1 hq0 hq1 hr0 hr1 hs0 hs1 σ h hx hy]
      exact le_max_of_le_right (mul_le_mul_of_nonneg_left
        (add_le_add le_rfl (le_ciSup BB (shift σ))) hq0.le)
  · set f := ⨆ σ, expectedReturn p q r s σ x y with hf
    apply max_le
    · have : ∀ τ, expectedReturn p q r s τ ((1 - r) * x) y ≤ f / p - r * x := by
        intro τ
        have h1 := le_ciSup B0 (cons Mine.A τ)
        rw [ret_A hp0 hp1 hq0 hq1 hr0 hr1 hs0 hs1 (cons Mine.A τ) rfl hx hy, shift_cons] at h1
        rw [le_sub_iff_add_le, le_div_iff₀ hp0]; linarith
      have h2 := ciSup_le this
      have h3 := mul_le_mul_of_nonneg_left (add_le_add (le_refl (r * x)) h2) hp0.le
      have e : p * (r * x + (f / p - r * x)) = f := by field_simp; ring
      linarith
    · have : ∀ τ, expectedReturn p q r s τ x ((1 - s) * y) ≤ f / q - s * y := by
        intro τ
        have h1 := le_ciSup B0 (cons Mine.B τ)
        rw [ret_B hp0 hp1 hq0 hq1 hr0 hr1 hs0 hs1 (cons Mine.B τ) rfl hx hy, shift_cons] at h1
        rw [le_sub_iff_add_le, le_div_iff₀ hq0]; linarith
      have h2 := ciSup_le this
      have h3 := mul_le_mul_of_nonneg_left (add_le_add (le_refl (s * y)) h2) hq0.le
      have e : q * (s * y + (f / q - s * y)) = f := by field_simp; ring
      linarith

end Main

end BellmanTheoryDP.GoldMining

open BellmanTheoryDP.GoldMining

theorem solution (p q r s x y : ℝ)
    (hp0 : 0 < p) (hp1 : p < 1) (hq0 : 0 < q) (hq1 : q < 1)
    (hr0 : 0 < r) (hr1 : r < 1) (hs0 : 0 < s) (hs1 : s < 1)
    (hx : 0 ≤ x) (hy : 0 ≤ y) :
    optimalReturn p q r s x y =
      max (p * (r * x + optimalReturn p q r s ((1 - r) * x) y))
          (q * (s * y + optimalReturn p q r s x ((1 - s) * y))) := by
  exact functional_eq_main hp0 hp1 hq0 hq1 hr0 hr1 hs0 hs1 x y hx hy
