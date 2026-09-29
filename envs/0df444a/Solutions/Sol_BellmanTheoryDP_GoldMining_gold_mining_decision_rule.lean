-- Prove2me | solution 1 for BellmanTheoryDP.GoldMining.gold_mining_decision_rule
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-28T14:44:49.059079+00:00
-- url     : https://prove2.me/submissions/917aed97-fea2-4218-9baf-cd190100301d

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


section Rule

variable {p q r s : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (hq0 : 0 < q) (hq1 : q < 1)
  (hr0 : 0 < r) (hr1 : r < 1) (hs0 : 0 < s) (hs1 : s < 1)
include hp0 hp1 hq0 hq1 hr0 hr1 hs0 hs1

lemma allB_indep (σ : ChoiceSeq) (hB : ∀ n, σ n = Mine.B) (x x' y : ℝ) :
    expectedReturn p q r s σ x y = expectedReturn p q r s σ x' y := by
  unfold expectedReturn
  congr 1; funext n
  simp only [gain, hB n]

lemma allB_le (σ : ChoiceSeq) (hB : ∀ n, σ n = Mine.B) {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    (1 - q) * expectedReturn p q r s σ x y ≤ q * s * y := by
  have hsum := summable_ret hp0 hp1 hq0 hq1 hr0 hr1 hs0 hs1 σ hx hy
  have hg := (summable_geometric_of_lt_one hq0.le hq1).mul_left (q * (s * y))
  have hle : expectedReturn p q r s σ x y ≤ ∑' n : ℕ, q * (s * y) * q ^ n := by
    refine hsum.tsum_le_tsum (fun n => ?_) hg
    have hsv : survival p q σ n = q ^ (n + 1) := by
      unfold survival; simp [hB, successProb]
    have hgn : gain r s σ x y n ≤ s * y := by
      unfold gain; rw [hB n]; simp only
      have : (1 - s) ^ usesB σ n ≤ 1 := pow_le_one₀ (by linarith) (by linarith)
      have : 0 ≤ s * y := mul_nonneg hs0.le hy
      nlinarith
    rw [hsv]
    calc q ^ (n + 1) * gain r s σ x y n ≤ q ^ (n + 1) * (s * y) :=
          mul_le_mul_of_nonneg_left hgn (pow_nonneg hq0.le _)
      _ = q * (s * y) * q ^ n := by ring
  rw [tsum_mul_left, tsum_geometric_of_lt_one hq0.le hq1] at hle
  have hq' : 0 < 1 - q := by linarith
  have := mul_le_mul_of_nonneg_left hle hq'.le
  rw [show (1 - q) * (q * (s * y) * (1 - q)⁻¹) = q * s * y by field_simp] at this
  exact this

lemma swap_k (k : ℕ) : ∀ (σ : ChoiceSeq) (x y : ℝ), 0 ≤ x → 0 ≤ y →
    (∀ j < k, σ j = Mine.B) → σ k = Mine.A →
    (1 - p) * (q * s * y) ≤ (1 - q) * (p * r * x) →
    ∃ σ' : ChoiceSeq, σ' 0 = Mine.A ∧
      expectedReturn p q r s σ x y +
        (if k = 0 then 0 else (1 - q) * (p * r * x) - (1 - p) * (q * s * y)) ≤
      expectedReturn p q r s σ' x y := by
  induction k with
  | zero =>
    intro σ x y _ _ _ hA _
    exact ⟨σ, hA, by simp⟩
  | succ k ih =>
    intro σ x y hx hy hB hA hH
    have h0 : σ 0 = Mine.B := hB 0 (Nat.succ_pos k)
    have hy' : 0 ≤ (1 - s) * y := mul_nonneg (by linarith) hy
    have hx' : 0 ≤ (1 - r) * x := mul_nonneg (by linarith) hx
    have hH' : (1 - p) * (q * s * ((1 - s) * y)) ≤ (1 - q) * (p * r * x) := by
      have : q * s * ((1 - s) * y) ≤ q * s * y := by
        have : (1 - s) * y ≤ y := by nlinarith
        exact mul_le_mul_of_nonneg_left this (by positivity)
      nlinarith
    obtain ⟨τ', hτ'0, hτ'⟩ := ih (shift σ) x ((1 - s) * y) hx hy'
      (fun j hj => hB (j + 1) (by omega)) hA hH'
    have hgap : 0 ≤ (if k = 0 then (0 : ℝ) else
        (1 - q) * (p * r * x) - (1 - p) * (q * s * ((1 - s) * y))) := by
      split_ifs <;> linarith
    refine ⟨cons Mine.A (cons Mine.B (shift τ')), rfl, ?_⟩
    rw [ret_B hp0 hp1 hq0 hq1 hr0 hr1 hs0 hs1 σ h0 hx hy,
      ret_A hp0 hp1 hq0 hq1 hr0 hr1 hs0 hs1 (cons Mine.A (cons Mine.B (shift τ'))) rfl hx hy,
      shift_cons,
      ret_B hp0 hp1 hq0 hq1 hr0 hr1 hs0 hs1 (cons Mine.B (shift τ')) rfl hx' hy, shift_cons]
    rw [ret_A hp0 hp1 hq0 hq1 hr0 hr1 hs0 hs1 τ' hτ'0 hx hy'] at hτ'
    simp only [Nat.add_one_ne_zero, if_false]
    nlinarith

lemma key_swap (σ : ChoiceSeq) (h0 : σ 0 = Mine.B) {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hH : (1 - p) * (q * s * y) ≤ (1 - q) * (p * r * x)) :
    ∃ σ' : ChoiceSeq, σ' 0 = Mine.A ∧
      expectedReturn p q r s σ x y + ((1 - q) * (p * r * x) - (1 - p) * (q * s * y)) ≤
      expectedReturn p q r s σ' x y := by
  classical
  by_cases hA : ∃ k, σ k = Mine.A
  · set k := Nat.find hA with hk
    have hkA : σ k = Mine.A := Nat.find_spec hA
    have hlt : ∀ j < k, σ j = Mine.B := fun j hj => by
      have := Nat.find_min hA hj
      cases h : σ j
      · exact absurd h this
      · rfl
    have hk0 : k ≠ 0 := by intro h; rw [h, h0] at hkA; cases hkA
    obtain ⟨σ', hσ'0, hσ'⟩ := swap_k hp0 hp1 hq0 hq1 hr0 hr1 hs0 hs1 k σ x y hx hy hlt hkA hH
    rw [if_neg hk0] at hσ'
    exact ⟨σ', hσ'0, hσ'⟩
  · push_neg at hA
    have hB : ∀ n, σ n = Mine.B := fun n => by
      cases h : σ n
      · exact absurd h (hA n)
      · rfl
    refine ⟨cons Mine.A σ, rfl, ?_⟩
    have hx' : 0 ≤ (1 - r) * x := mul_nonneg (by linarith) hx
    rw [ret_A hp0 hp1 hq0 hq1 hr0 hr1 hs0 hs1 (cons Mine.A σ) rfl hx hy, shift_cons,
      allB_indep hp0 hp1 hq0 hq1 hr0 hr1 hs0 hs1 σ hB ((1 - r) * x) x y]
    have hJ := allB_le hp0 hp1 hq0 hq1 hr0 hr1 hs0 hs1 σ hB hx hy
    have hJ0 := ret_nonneg hp0 hp1 hq0 hq1 hr0 hr1 hs0 hs1 σ hx hy
    set J := expectedReturn p q r s σ x y
    have hq' : 0 < 1 - q := by linarith
    have hp' : 0 < 1 - p := by linarith
    -- (1-p)(1-q) J ≤ (1-q)(q p r x + (1-p) q s y)
    have h1 : (1 - p) * ((1 - q) * J) ≤ (1 - p) * (q * s * y) :=
      mul_le_mul_of_nonneg_left hJ hp'.le
    have h2 : q * ((1 - p) * (q * s * y)) ≤ q * ((1 - q) * (p * r * x)) :=
      mul_le_mul_of_nonneg_left hH hq0.le
    have h3 : (1 - q) * ((1 - p) * J) ≤ (1 - q) * (q * (p * r * x) + (1 - p) * (q * s * y)) := by
      nlinarith
    have h4 : (1 - p) * J ≤ q * (p * r * x) + (1 - p) * (q * s * y) :=
      le_of_mul_le_mul_left h3 hq'
    nlinarith

lemma VB_le {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hH : (1 - p) * (q * s * y) ≤ (1 - q) * (p * r * x)) :
    q * (s * y + optimalReturn p q r s x ((1 - s) * y)) +
        ((1 - q) * (p * r * x) - (1 - p) * (q * s * y)) ≤
      p * (r * x + optimalReturn p q r s ((1 - r) * x) y) := by
  haveI : Nonempty ChoiceSeq := ⟨fun _ => Mine.A⟩
  have hx' : 0 ≤ (1 - r) * x := mul_nonneg (by linarith) hx
  have BA := bdd_ret hp0 hp1 hq0 hq1 hr0 hr1 hs0 hs1 hx' hy
  set D := (1 - q) * (p * r * x) - (1 - p) * (q * s * y)
  set VA := p * (r * x + optimalReturn p q r s ((1 - r) * x) y)
  have hτ : ∀ τ, expectedReturn p q r s τ x ((1 - s) * y) ≤ (VA - D) / q - s * y := by
    intro τ
    obtain ⟨σ', hσ'0, hσ'⟩ := key_swap hp0 hp1 hq0 hq1 hr0 hr1 hs0 hs1 (cons Mine.B τ) rfl hx hy hH
    rw [ret_B hp0 hp1 hq0 hq1 hr0 hr1 hs0 hs1 (cons Mine.B τ) rfl hx hy, shift_cons,
      ret_A hp0 hp1 hq0 hq1 hr0 hr1 hs0 hs1 σ' hσ'0 hx hy] at hσ'
    have h1 : expectedReturn p q r s (shift σ') ((1 - r) * x) y ≤
        optimalReturn p q r s ((1 - r) * x) y := le_ciSup BA (shift σ')
    have h2 : p * (r * x + expectedReturn p q r s (shift σ') ((1 - r) * x) y) ≤ VA :=
      mul_le_mul_of_nonneg_left (add_le_add le_rfl h1) hp0.le
    rw [le_sub_iff_add_le, le_div_iff₀ hq0]; nlinarith
  have := ciSup_le hτ
  have h3 := mul_le_mul_of_nonneg_left (add_le_add (le_refl (s * y)) this) hq0.le
  have e : q * (s * y + ((VA - D) / q - s * y)) = VA - D := by field_simp; ring
  unfold optimalReturn at h3 ⊢
  linarith

end Rule

/-- swap the two mines -/
def swapM : Mine → Mine
  | Mine.A => Mine.B
  | Mine.B => Mine.A

@[simp] lemma swapM_A : swapM Mine.A = Mine.B := rfl
@[simp] lemma swapM_B : swapM Mine.B = Mine.A := rfl

lemma swapM_invol : Function.Involutive swapM := fun m => by cases m <;> rfl

lemma usesA_swap (σ : ChoiceSeq) (n : ℕ) : usesA (fun k => swapM (σ k)) n = usesB σ n := by
  unfold usesA usesB
  congr 1; ext k; simp only [Finset.mem_filter]
  cases σ k <;> simp

lemma usesB_swap (σ : ChoiceSeq) (n : ℕ) : usesB (fun k => swapM (σ k)) n = usesA σ n := by
  unfold usesA usesB
  congr 1; ext k; simp only [Finset.mem_filter]
  cases σ k <;> simp

lemma ret_swap (p q r s : ℝ) (σ : ChoiceSeq) (x y : ℝ) :
    expectedReturn q p s r (fun k => swapM (σ k)) y x = expectedReturn p q r s σ x y := by
  unfold expectedReturn
  congr 1; funext n
  have hs : survival q p (fun k => swapM (σ k)) n = survival p q σ n := by
    unfold survival; congr 1; funext k; cases h : σ k <;> simp [h, successProb]
  have hg : gain s r (fun k => swapM (σ k)) y x n = gain r s σ x y n := by
    unfold gain
    rw [usesA_swap, usesB_swap]
    cases h : σ n <;> simp [h]
  rw [hs, hg]

lemma opt_swap (p q r s x y : ℝ) : optimalReturn q p s r y x = optimalReturn p q r s x y := by
  unfold optimalReturn
  have e : (fun σ => expectedReturn q p s r σ y x) =
      (fun σ => expectedReturn p q r s σ x y) ∘ (fun σ : ChoiceSeq => fun k => swapM (σ k)) := by
    funext σ
    simp only [Function.comp]
    rw [← ret_swap p q r s (fun k => swapM (σ k)) x y]
    congr 1; funext k; simp [swapM_invol (σ k)]
  rw [e]
  have hinv : Function.Involutive (fun σ : ChoiceSeq => fun k => swapM (σ k)) := fun σ => by
    funext k; simp [swapM_invol (σ k)]
  exact Equiv.iSup_comp (g := fun σ => expectedReturn p q r s σ x y) (hinv.toPerm _)

theorem decision_rule_main (p q r s x y : ℝ)
    (hp0 : 0 < p) (hp1 : p < 1) (hq0 : 0 < q) (hq1 : q < 1)
    (hr0 : 0 < r) (hr1 : r < 1) (hs0 : 0 < s) (hs1 : s < 1)
    (hx : 0 ≤ x) (hy : 0 ≤ y) :
    (q * s * y / (1 - q) < p * r * x / (1 - p) →
        q * (s * y + optimalReturn p q r s x ((1 - s) * y)) <
          p * (r * x + optimalReturn p q r s ((1 - r) * x) y)) ∧
    (p * r * x / (1 - p) < q * s * y / (1 - q) →
        p * (r * x + optimalReturn p q r s ((1 - r) * x) y) <
          q * (s * y + optimalReturn p q r s x ((1 - s) * y))) ∧
    (p * r * x / (1 - p) = q * s * y / (1 - q) →
        p * (r * x + optimalReturn p q r s ((1 - r) * x) y) =
          q * (s * y + optimalReturn p q r s x ((1 - s) * y))) := by
  have hp' : 0 < 1 - p := by linarith
  have hq' : 0 < 1 - q := by linarith
  -- the symmetric instance
  have sym : (1 - q) * (p * r * x) ≤ (1 - p) * (q * s * y) →
      p * (r * x + optimalReturn p q r s ((1 - r) * x) y) +
        ((1 - p) * (q * s * y) - (1 - q) * (p * r * x)) ≤
      q * (s * y + optimalReturn p q r s x ((1 - s) * y)) := by
    intro hH
    have := VB_le hq0 hq1 hp0 hp1 hs0 hs1 hr0 hr1 (x := y) (y := x) hy hx (by linarith)
    rw [opt_swap p q r s ((1 - r) * x) y, opt_swap p q r s x ((1 - s) * y)] at this
    linarith
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
  · rw [div_lt_div_iff₀ hq' hp'] at h
    have := VB_le hp0 hp1 hq0 hq1 hr0 hr1 hs0 hs1 hx hy (by linarith)
    linarith
  · rw [div_lt_div_iff₀ hp' hq'] at h
    have := sym (by linarith)
    linarith
  · rw [div_eq_div_iff hp'.ne' hq'.ne'] at h
    have h1 := VB_le hp0 hp1 hq0 hq1 hr0 hr1 hs0 hs1 hx hy (by linarith)
    have h2 := sym (by linarith)
    linarith

end BellmanTheoryDP.GoldMining

open BellmanTheoryDP.GoldMining

theorem solution (p q r s x y : ℝ)
    (hp0 : 0 < p) (hp1 : p < 1) (hq0 : 0 < q) (hq1 : q < 1)
    (hr0 : 0 < r) (hr1 : r < 1) (hs0 : 0 < s) (hs1 : s < 1)
    (hx : 0 ≤ x) (hy : 0 ≤ y) :
    (q * s * y / (1 - q) < p * r * x / (1 - p) →
        q * (s * y + optimalReturn p q r s x ((1 - s) * y)) <
          p * (r * x + optimalReturn p q r s ((1 - r) * x) y)) ∧
    (p * r * x / (1 - p) < q * s * y / (1 - q) →
        p * (r * x + optimalReturn p q r s ((1 - r) * x) y) <
          q * (s * y + optimalReturn p q r s x ((1 - s) * y))) ∧
    (p * r * x / (1 - p) = q * s * y / (1 - q) →
        p * (r * x + optimalReturn p q r s ((1 - r) * x) y) =
          q * (s * y + optimalReturn p q r s x ((1 - s) * y))) := by
  exact decision_rule_main p q r s x y hp0 hp1 hq0 hq1 hr0 hr1 hs0 hs1 hx hy
