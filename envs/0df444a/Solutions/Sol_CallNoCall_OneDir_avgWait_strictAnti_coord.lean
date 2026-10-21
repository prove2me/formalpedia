-- Prove2me | solution 1 for CallNoCall.OneDir.avgWait_strictAnti_coord
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T15:06:50.444996+00:00
-- url     : https://prove2.me/submissions/19df90f3-5618-4257-90f6-5cbcb77de6e6

import Mathlib
import Definitions.Def_CallNoCall_OneDir_StateDepQueue

set_option autoImplicit false
open CallNoCall.OneDir

namespace AuxCNC

lemma prodRates_pos (μ : ℕ → ℝ) (hμ : ∀ n, 1 ≤ n → 0 < μ n) (i : ℕ) : 0 < prodRates μ i := by
  unfold prodRates
  apply Finset.prod_pos
  intro j hj
  exact hμ j (Finset.mem_Icc.mp hj).1

lemma prodRates_succ (μ : ℕ → ℝ) (i : ℕ) :
    prodRates μ (i + 1) = prodRates μ i * μ (i + 1) := by
  unfold prodRates
  exact Finset.prod_Icc_succ_top (by omega) _

lemma prodRates_one (μ : ℕ → ℝ) : prodRates μ 1 = μ 1 := by
  simp [prodRates]

lemma prodRates_le (μ μ' : ℕ → ℝ) (hμ : ∀ n, 1 ≤ n → 0 < μ n)
    (hle : ∀ n, 1 ≤ n → μ n ≤ μ' n) (i : ℕ) : prodRates μ i ≤ prodRates μ' i := by
  unfold prodRates
  apply Finset.prod_le_prod
  · intro j hj
    exact (hμ j (Finset.mem_Icc.mp hj).1).le
  · intro j hj
    exact hle j (Finset.mem_Icc.mp hj).1

lemma ratio_antitone (μ μ' : ℕ → ℝ) (hμ : ∀ n, 1 ≤ n → 0 < μ n)
    (hle : ∀ n, 1 ≤ n → μ n ≤ μ' n) :
    Antitone (fun i => prodRates μ i / prodRates μ' i) := by
  apply antitone_nat_of_succ_le
  intro i
  have hP := prodRates_pos μ hμ i
  have hP' := prodRates_pos μ' (fun n hn => lt_of_lt_of_le (hμ n hn) (hle n hn)) i
  have h1 := hμ (i + 1) (by omega)
  have h2 := hle (i + 1) (by omega)
  show prodRates μ (i + 1) / prodRates μ' (i + 1) ≤ prodRates μ i / prodRates μ' i
  rw [prodRates_succ, prodRates_succ]
  have h3 : 0 < prodRates μ' i * μ' (i + 1) := mul_pos hP' (lt_of_lt_of_le h1 h2)
  rw [div_le_div_iff₀ h3 hP']
  have := mul_le_mul_of_nonneg_left h2 (le_of_lt (mul_pos hP hP'))
  nlinarith

lemma numTerm_nonneg (μ : ℕ → ℝ) (lam : ℝ) (hμ : ∀ n, 1 ≤ n → 0 < μ n) (hlam : 0 ≤ lam)
    (i : ℕ) : 0 ≤ numTerm μ lam i := by
  unfold numTerm
  have := prodRates_pos μ hμ i
  positivity

lemma denTerm_nonneg (μ : ℕ → ℝ) (lam : ℝ) (hμ : ∀ n, 1 ≤ n → 0 < μ n) (hlam : 0 ≤ lam)
    (i : ℕ) : 0 ≤ denTerm μ lam i := by
  unfold denTerm
  have := prodRates_pos μ hμ i
  positivity

lemma fw_mono (μ μ' : ℕ → ℝ) (lam : ℝ) (hμ : ∀ n, 1 ≤ n → 0 < μ n)
    (hle : ∀ n, 1 ≤ n → μ n ≤ μ' n) (hlam : 0 ≤ lam) (hfin : FiniteWait μ lam) :
    FiniteWait μ' lam := by
  have hμ' : ∀ n, 1 ≤ n → 0 < μ' n := fun n hn => lt_of_lt_of_le (hμ n hn) (hle n hn)
  constructor
  · refine Summable.of_nonneg_of_le (fun i => numTerm_nonneg μ' lam hμ' hlam _) (fun i => ?_) hfin.1
    unfold numTerm
    have h1 := prodRates_pos μ hμ (i + 1)
    have h2 := prodRates_le μ μ' hμ hle (i + 1)
    have h0 : 0 ≤ ((i + 1 : ℕ) : ℝ) * lam ^ (i + 1 - 1) := by positivity
    exact div_le_div_of_nonneg_left h0 h1 h2
  · refine Summable.of_nonneg_of_le (fun i => denTerm_nonneg μ' lam hμ' hlam _) (fun i => ?_) hfin.2
    unfold denTerm
    have h1 := prodRates_pos μ hμ (i + 1)
    have h2 := prodRates_le μ μ' hμ hle (i + 1)
    have h0 : 0 ≤ lam ^ (i + 1) := by positivity
    exact div_le_div_of_nonneg_left h0 h1 h2

lemma numTerm_eq (μ : ℕ → ℝ) (lam : ℝ) (hlam : lam ≠ 0) (i : ℕ)
    (hP : prodRates μ i ≠ 0) :
    numTerm μ lam i = (i : ℝ) * (lam ^ i / prodRates μ i) / lam := by
  unfold numTerm
  cases i with
  | zero => simp
  | succ k =>
    rw [Nat.add_sub_cancel, pow_succ]
    field_simp

lemma sums_eq (μ : ℕ → ℝ) (lam : ℝ) (hlam : 0 < lam) (hμ : ∀ n, 1 ≤ n → 0 < μ n)
    (hfin : FiniteWait μ lam) :
    (∑' i : ℕ, numTerm μ lam (i + 1)) = (∑' i : ℕ, (i : ℝ) * (lam ^ i / prodRates μ i)) / lam ∧
    1 + ∑' i : ℕ, denTerm μ lam (i + 1) = ∑' i : ℕ, lam ^ i / prodRates μ i := by
  have hP := fun i => (prodRates_pos μ hμ i).ne'
  have hn : Summable (numTerm μ lam) := (summable_nat_add_iff 1).mp hfin.1
  have hd : Summable (denTerm μ lam) := (summable_nat_add_iff 1).mp hfin.2
  constructor
  · have := hn.tsum_eq_zero_add
    have h0 : numTerm μ lam 0 = 0 := by simp [numTerm]
    rw [h0, zero_add] at this
    rw [← this, ← tsum_div_const]
    exact tsum_congr (fun i => numTerm_eq μ lam hlam.ne' i (hP i))
  · have := hd.tsum_eq_zero_add
    have h0 : denTerm μ lam 0 = 1 := by simp [denTerm, prodRates]
    rw [h0] at this
    exact this.symm

lemma key (a r : ℕ → ℝ) (ha : ∀ i, 0 ≤ a i) (hr0 : ∀ i, 0 ≤ r i) (hr : Antitone r)
    (hsa : Summable a) (hsb : Summable (fun i : ℕ => (i : ℝ) * a i)) (hApos : 0 < ∑' i, a i)
    (n : ℕ) :
    Summable (fun i : ℕ => (i : ℝ) * (a i * r i)) ∧ Summable (fun i => a i * r i) ∧
    HasSum (fun i : ℕ => a i * (((i : ℝ) - (∑' i : ℕ, (i : ℝ) * a i) / (∑' i, a i)) * (r i - r n)))
      ((∑' i : ℕ, (i : ℝ) * (a i * r i)) - (∑' i : ℕ, (i : ℝ) * a i) / (∑' i, a i) * ∑' i, a i * r i) := by
  have hs2 : Summable (fun i => a i * r i) :=
    Summable.of_nonneg_of_le (fun i => mul_nonneg (ha i) (hr0 i))
      (fun i => mul_le_mul_of_nonneg_left (hr (Nat.zero_le i)) (ha i)) (hsa.mul_right (r 0))
  have hs1 : Summable (fun i : ℕ => (i : ℝ) * (a i * r i)) :=
    Summable.of_nonneg_of_le (fun i => mul_nonneg (Nat.cast_nonneg i) (mul_nonneg (ha i) (hr0 i)))
      (fun i => by
        have := mul_le_mul_of_nonneg_left (hr (Nat.zero_le i)) (mul_nonneg (Nat.cast_nonneg i) (ha i))
        calc (i : ℝ) * (a i * r i) = (i : ℝ) * a i * r i := by ring
          _ ≤ (i : ℝ) * a i * r 0 := this)
      (hsb.mul_right (r 0))
  refine ⟨hs1, hs2, ?_⟩
  set L : ℝ := (∑' i : ℕ, (i : ℝ) * a i) / (∑' i, a i) with hL
  have h1 := hs1.hasSum
  have h2 := hs2.hasSum
  have h3 := hsb.hasSum
  have h4 := hsa.hasSum
  have h := (((h1.sub (h2.mul_left L)).sub (h3.mul_left (r n))).add (h4.mul_left (r n * L)))
  have hA : (∑' i : ℕ, (i : ℝ) * a i) = L * ∑' i, a i := by
    rw [hL, div_mul_cancel₀ _ hApos.ne']
  have e1 : (fun i : ℕ => a i * (((i : ℝ) - L) * (r i - r n))) =
      fun b : ℕ => (b : ℝ) * (a b * r b) - L * (a b * r b) - r n * ((b : ℝ) * a b)
        + r n * L * a b := by
    funext i; ring
  have e2 : (∑' i : ℕ, (i : ℝ) * (a i * r i)) - L * ∑' i, a i * r i =
      (∑' i : ℕ, (i : ℝ) * (a i * r i)) - L * ∑' i, a i * r i
        - r n * (∑' i : ℕ, (i : ℝ) * a i) + r n * L * ∑' i, a i := by
    rw [hA]; ring
  rw [e1, e2]
  exact h

lemma core (a r : ℕ → ℝ) (ha : ∀ i, 0 < a i) (hr0 : ∀ i, 0 ≤ r i) (hr : Antitone r)
    (hsa : Summable a) (hsb : Summable (fun i : ℕ => (i : ℝ) * a i)) :
    (∑' i : ℕ, (i : ℝ) * (a i * r i)) * (∑' i, a i) ≤ (∑' i : ℕ, (i : ℝ) * a i) * ∑' i, a i * r i ∧
    ((∃ p, r (p + 1) < r p) →
      (∑' i : ℕ, (i : ℝ) * (a i * r i)) * (∑' i, a i) < (∑' i : ℕ, (i : ℝ) * a i) * ∑' i, a i * r i) := by
  have ha' : ∀ i, 0 ≤ a i := fun i => (ha i).le
  have hApos : 0 < ∑' i, a i := hsa.tsum_pos ha' 0 (ha 0)
  have hBpos : 0 < ∑' i : ℕ, (i : ℝ) * a i :=
    hsb.tsum_pos (fun i => mul_nonneg (Nat.cast_nonneg i) (ha' i)) 1 (by
      have := ha 1
      simpa using this)
  set A := ∑' i, a i with hAdef
  set B := ∑' i : ℕ, (i : ℝ) * a i with hBdef
  set L : ℝ := B / A with hL
  have hLpos : 0 < L := div_pos hBpos hApos
  have hLA : L * A = B := by rw [hL, div_mul_cancel₀ _ hApos.ne']
  set n : ℕ := ⌊L⌋₊ + 1 with hn
  obtain ⟨hs1, hs2, hS⟩ := key a r ha' hr0 hr hsa hsb hApos n
  have hsign : ∀ i : ℕ, ((i : ℝ) - L) * (r i - r n) ≤ 0 := by
    intro i
    by_cases hi : (i : ℝ) ≤ L
    · have h1 : i ≤ ⌊L⌋₊ := Nat.le_floor hi
      have h2 : r n ≤ r i := hr (by omega)
      exact mul_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)
    · push_neg at hi
      have h1 : ⌊L⌋₊ < i := (Nat.floor_lt hLpos.le).mpr hi
      have h2 : r i ≤ r n := hr (by omega)
      exact mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)
  have hfin : ∑' i, a i * (((i : ℝ) - L) * (r i - r n)) =
      (∑' i : ℕ, (i : ℝ) * (a i * r i)) - L * ∑' i, a i * r i := hS.tsum_eq
  have hconv : ∀ S : ℝ, S ≤ L * (∑' i, a i * r i) → S * A ≤ B * ∑' i, a i * r i := by
    intro S hSle
    calc S * A ≤ L * (∑' i, a i * r i) * A := mul_le_mul_of_nonneg_right hSle hApos.le
      _ = (L * A) * ∑' i, a i * r i := by ring
      _ = B * ∑' i, a i * r i := by rw [hLA]
  have hconv' : ∀ S : ℝ, S < L * (∑' i, a i * r i) → S * A < B * ∑' i, a i * r i := by
    intro S hSle
    calc S * A < L * (∑' i, a i * r i) * A := mul_lt_mul_of_pos_right hSle hApos
      _ = (L * A) * ∑' i, a i * r i := by ring
      _ = B * ∑' i, a i * r i := by rw [hLA]
  refine ⟨?_, ?_⟩
  · apply hconv
    have : ∑' i, a i * (((i : ℝ) - L) * (r i - r n)) ≤ 0 :=
      tsum_nonpos (fun i => mul_nonpos_of_nonneg_of_nonpos (ha' i) (hsign i))
    linarith
  · rintro ⟨p, hp⟩
    apply hconv'
    have hex : ∃ i0 : ℕ, a i0 * (((i0 : ℝ) - L) * (r i0 - r n)) < 0 := by
      by_cases hnp : n ≤ p
      · refine ⟨p + 1, ?_⟩
        have h1 : L < n := by
          have := Nat.lt_floor_add_one L
          simpa [hn] using this
        have h2 : r p ≤ r n := hr hnp
        have h3 : (0 : ℝ) < ((p + 1 : ℕ) : ℝ) - L := by
          have : (n : ℝ) ≤ p := by exact_mod_cast hnp
          push_cast
          linarith
        exact mul_neg_of_pos_of_neg (ha _) (mul_neg_of_pos_of_neg h3 (by linarith))
      · refine ⟨0, ?_⟩
        push_neg at hnp
        have h2 : r n ≤ r (p + 1) := hr (by omega)
        have h3 : r p ≤ r 0 := hr (Nat.zero_le p)
        exact mul_neg_of_pos_of_neg (ha _)
          (mul_neg_of_neg_of_pos (by simpa using hLpos) (by linarith))
    obtain ⟨i0, hi0⟩ := hex
    have hlt : (∑' i : ℕ, (i : ℝ) * (a i * r i)) - L * ∑' i, a i * r i < 0 :=
      hasSum_lt (f := fun i => a i * (((i : ℝ) - L) * (r i - r n))) (g := fun _ => (0 : ℝ))
        (fun i => mul_nonpos_of_nonneg_of_nonpos (ha' i) (hsign i)) hi0 hS hasSum_zero
    linarith

end AuxCNC

namespace AuxCNC

lemma mono_pos (μ μ' : ℕ → ℝ) (lam : ℝ) (hμ : ∀ n, 1 ≤ n → 0 < μ n)
    (hle : ∀ n, 1 ≤ n → μ n ≤ μ' n) (hlam : 0 < lam) (hfin : FiniteWait μ lam) :
    FiniteWait μ' lam ∧
    ((∑' i : ℕ, numTerm μ' lam (i + 1)) / (1 + ∑' i : ℕ, denTerm μ' lam (i + 1)) ≤
      (∑' i : ℕ, numTerm μ lam (i + 1)) / (1 + ∑' i : ℕ, denTerm μ lam (i + 1))) ∧
    ((∃ k, 1 ≤ k ∧ μ k < μ' k) →
      (∑' i : ℕ, numTerm μ' lam (i + 1)) / (1 + ∑' i : ℕ, denTerm μ' lam (i + 1)) <
      (∑' i : ℕ, numTerm μ lam (i + 1)) / (1 + ∑' i : ℕ, denTerm μ lam (i + 1))) := by
  have hμ' : ∀ n, 1 ≤ n → 0 < μ' n := fun n hn => lt_of_lt_of_le (hμ n hn) (hle n hn)
  have hfin' := fw_mono μ μ' lam hμ hle hlam.le hfin
  refine ⟨hfin', ?_⟩
  obtain ⟨hN, hD⟩ := sums_eq μ lam hlam hμ hfin
  obtain ⟨hN', hD'⟩ := sums_eq μ' lam hlam hμ' hfin'
  rw [hN, hD, hN', hD']
  set a : ℕ → ℝ := fun i => lam ^ i / prodRates μ i with ha
  set r : ℕ → ℝ := fun i => prodRates μ i / prodRates μ' i with hr
  have hP := fun i => (prodRates_pos μ hμ i)
  have hP' := fun i => (prodRates_pos μ' hμ' i)
  have hapos : ∀ i, 0 < a i := fun i => div_pos (pow_pos hlam i) (hP i)
  have hrpos : ∀ i, 0 ≤ r i := fun i => (div_pos (hP i) (hP' i)).le
  have hrmono : Antitone r := ratio_antitone μ μ' hμ hle
  have hsa : Summable a := (summable_nat_add_iff 1).mp hfin.2
  have hsb : Summable (fun i : ℕ => (i : ℝ) * a i) := by
    have hn : Summable (numTerm μ lam) := (summable_nat_add_iff 1).mp hfin.1
    have := hn.mul_left lam
    refine this.congr (fun i => ?_)
    rw [numTerm_eq μ lam hlam.ne' i (hP i).ne']
    simp only [ha]
    field_simp
  have heq : ∀ i, lam ^ i / prodRates μ' i = a i * r i := by
    intro i
    simp only [ha, hr]
    have := (hP i).ne'
    have := (hP' i).ne'
    field_simp
  have heq2 : ∀ i : ℕ, (i : ℝ) * (lam ^ i / prodRates μ' i) = (i : ℝ) * (a i * r i) := by
    intro i; rw [heq]
  simp_rw [heq2, heq]
  obtain ⟨c1, c2⟩ := core a r hapos hrpos hrmono hsa hsb
  have hApos : 0 < ∑' i, a i := hsa.tsum_pos (fun i => (hapos i).le) 0 (hapos 0)
  have hT0pos : 0 < ∑' i, a i * r i := by
    have hs2 : Summable (fun i => a i * r i) :=
      Summable.of_nonneg_of_le (fun i => mul_nonneg (hapos i).le (hrpos i))
        (fun i => mul_le_mul_of_nonneg_left (hrmono (Nat.zero_le i)) (hapos i).le)
        (hsa.mul_right (r 0))
    refine hs2.tsum_pos (fun i => mul_nonneg (hapos i).le (hrpos i)) 0 ?_
    exact mul_pos (hapos 0) (div_pos (hP 0) (hP' 0))
  refine ⟨?_, ?_⟩
  · rw [div_div, div_div, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left c1 hlam.le]
  · rintro ⟨k, hk, hkl⟩
    have hp : ∃ p, r (p + 1) < r p := by
      obtain ⟨p, rfl⟩ : ∃ p, k = p + 1 := ⟨k - 1, by omega⟩
      refine ⟨p, ?_⟩
      have h1 := hP p
      have h2 := hP' p
      have h3 := hμ (p + 1) hk
      show prodRates μ (p + 1) / prodRates μ' (p + 1) < prodRates μ p / prodRates μ' p
      rw [prodRates_succ, prodRates_succ]
      have h4 : 0 < prodRates μ' p * μ' (p + 1) := mul_pos h2 (hμ' _ hk)
      rw [div_lt_div_iff₀ h4 h2]
      have := mul_lt_mul_of_pos_left hkl (mul_pos h1 h2)
      nlinarith
    have := c2 hp
    rw [div_div, div_div, div_lt_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_lt_mul_of_pos_left this hlam]

end AuxCNC

namespace AuxCNC

lemma prodRates_update_lt (μ : ℕ → ℝ) (m : ℕ) (z : ℝ) (i : ℕ) (h : i < m) :
    prodRates (Function.update μ m z) i = prodRates μ i := by
  unfold prodRates
  apply Finset.prod_congr rfl
  intro j hj
  have := (Finset.mem_Icc.mp hj).2
  rw [Function.update_of_ne (by omega)]

lemma prodRates_update_mul (μ : ℕ → ℝ) (m : ℕ) (hm : 1 ≤ m) (z : ℝ) (i : ℕ) (h : m ≤ i) :
    prodRates (Function.update μ m z) i = z * ∏ j ∈ Finset.Icc 1 i \ {m}, μ j := by
  unfold prodRates
  exact Finset.prod_update_of_mem (by simp only [Finset.mem_Icc]; omega) _ _

lemma prodRates_update_rel (μ : ℕ → ℝ) (m : ℕ) (hm : 1 ≤ m) (z w : ℝ) (i : ℕ) (h : m ≤ i) :
    prodRates (Function.update μ m z) i * w = z * prodRates (Function.update μ m w) i := by
  rw [prodRates_update_mul μ m hm z i h, prodRates_update_mul μ m hm w i h]
  ring

lemma update_pos (μ : ℕ → ℝ) (hμ : ∀ n, 1 ≤ n → 0 < μ n) (m : ℕ) (x : ℝ) (hx : 0 < x) :
    ∀ n, 1 ≤ n → 0 < Function.update μ m x n := by
  intro n hn
  by_cases h : n = m
  · subst h; simpa using hx
  · rw [Function.update_of_ne h]; exact hμ n hn

lemma update_ge (μ : ℕ → ℝ) (hμ : ∀ n, 1 ≤ n → 0 < μ n) (m : ℕ) (hm : 1 ≤ m) (x : ℝ)
    (hx : 0 < x) (i : ℕ) :
    prodRates μ i / (1 + μ m / x) ≤ prodRates (Function.update μ m x) i := by
  have hC : 0 < 1 + μ m / x := by have := hμ m hm; positivity
  have hP := prodRates_pos μ hμ i
  have hPx := prodRates_pos (Function.update μ m x) (update_pos μ hμ m x hx) i
  by_cases hi : i < m
  · rw [prodRates_update_lt μ m x i hi]
    exact div_le_self hP.le (by have := hμ m hm; have : 0 < μ m / x := by positivity
                                linarith)
  · push_neg at hi
    have h := prodRates_update_rel μ m hm x (μ m) i hi
    rw [Function.update_eq_self] at h
    rw [div_le_iff₀ hC]
    have h2 : prodRates (Function.update μ m x) i * (μ m / x) = prodRates μ i := by
      have := (hμ m hm)
      field_simp
      linarith
    nlinarith

lemma fw_update (μ : ℕ → ℝ) (lam : ℝ) (hμ : ∀ n, 1 ≤ n → 0 < μ n) (hlam : 0 ≤ lam)
    (hfin : FiniteWait μ lam) (m : ℕ) (hm : 1 ≤ m) (x : ℝ) (hx : 0 < x) :
    FiniteWait (Function.update μ m x) lam := by
  have hμx := update_pos μ hμ m x hx
  have hC : 0 < 1 + μ m / x := by have := hμ m hm; positivity
  constructor
  · refine Summable.of_nonneg_of_le (fun i => numTerm_nonneg _ lam hμx hlam _) (fun i => ?_)
      (hfin.1.mul_left (1 + μ m / x))
    unfold numTerm
    have h1 := prodRates_pos μ hμ (i + 1)
    have h0 : 0 ≤ ((i + 1 : ℕ) : ℝ) * lam ^ (i + 1 - 1) := by positivity
    have h2 := update_ge μ hμ m hm x hx (i + 1)
    calc ((i + 1 : ℕ) : ℝ) * lam ^ (i + 1 - 1) / prodRates (Function.update μ m x) (i + 1)
        ≤ ((i + 1 : ℕ) : ℝ) * lam ^ (i + 1 - 1) / (prodRates μ (i + 1) / (1 + μ m / x)) :=
          div_le_div_of_nonneg_left h0 (by positivity) h2
      _ = (1 + μ m / x) * (((i + 1 : ℕ) : ℝ) * lam ^ (i + 1 - 1) / prodRates μ (i + 1)) := by
          field_simp
  · refine Summable.of_nonneg_of_le (fun i => denTerm_nonneg _ lam hμx hlam _) (fun i => ?_)
      (hfin.2.mul_left (1 + μ m / x))
    unfold denTerm
    have h1 := prodRates_pos μ hμ (i + 1)
    have h0 : 0 ≤ lam ^ (i + 1) := by positivity
    have h2 := update_ge μ hμ m hm x hx (i + 1)
    calc lam ^ (i + 1) / prodRates (Function.update μ m x) (i + 1)
        ≤ lam ^ (i + 1) / (prodRates μ (i + 1) / (1 + μ m / x)) :=
          div_le_div_of_nonneg_left h0 (by positivity) h2
      _ = (1 + μ m / x) * (lam ^ (i + 1) / prodRates μ (i + 1)) := by
          field_simp

end AuxCNC

theorem solution (μ : ℕ → ℝ) (lam d v : ℝ) (hμ : ∀ n, 1 ≤ n → 0 < μ n)
    (hlam : 0 < lam) (hfin : FiniteWait μ lam) (m : ℕ) (hm : 1 ≤ m) (x y : ℝ) (hx : 0 < x)
    (hxy : x < y) :
    FiniteWait (Function.update μ m x) lam ∧ FiniteWait (Function.update μ m y) lam ∧
      avgWait (Function.update μ m y) lam d v < avgWait (Function.update μ m x) lam d v := by
  have hy : 0 < y := lt_trans hx hxy
  have hfx := AuxCNC.fw_update μ lam hμ hlam.le hfin m hm x hx
  have hfy := AuxCNC.fw_update μ lam hμ hlam.le hfin m hm y hy
  refine ⟨hfx, hfy, ?_⟩
  have hμx := AuxCNC.update_pos μ hμ m x hx
  have hle : ∀ n, 1 ≤ n → Function.update μ m x n ≤ Function.update μ m y n := by
    intro n hn
    by_cases h : n = m
    · subst h; simpa using hxy.le
    · rw [Function.update_of_ne h, Function.update_of_ne h]
  have := (AuxCNC.mono_pos (Function.update μ m x) (Function.update μ m y) lam hμx hle hlam
    hfx).2.2 ⟨m, hm, by simpa using hxy⟩
  unfold avgWait
  linarith
