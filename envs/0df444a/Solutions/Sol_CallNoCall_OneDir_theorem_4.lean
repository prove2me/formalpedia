-- Prove2me | solution 1 for CallNoCall.OneDir.theorem_4
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T15:52:40.50198+00:00
-- url     : https://prove2.me/submissions/26fb072a-5b82-44be-8ea2-a30f56b288dd

import Mathlib
import Definitions.Def_CallNoCall_OneDir_Setting

set_option autoImplicit false
open CallNoCall.OneDir

section Mono

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

theorem mono_solution (μ μ' : ℕ → ℝ) (lam d v : ℝ) (hμ : ∀ n, 1 ≤ n → 0 < μ n)
    (hle : ∀ n, 1 ≤ n → μ n ≤ μ' n) (hlam : 0 ≤ lam) (hfin : FiniteWait μ lam) :
    FiniteWait μ' lam ∧ avgWait μ' lam d v ≤ avgWait μ lam d v := by
  have hμ' : ∀ n, 1 ≤ n → 0 < μ' n := fun n hn => lt_of_lt_of_le (hμ n hn) (hle n hn)
  have hfin' := AuxCNC.fw_mono μ μ' lam hμ hle hlam hfin
  refine ⟨hfin', ?_⟩
  unfold avgWait
  rcases hlam.lt_or_eq with hpos | h0
  · have := (AuxCNC.mono_pos μ μ' lam hμ hle hpos hfin).2.1
    linarith
  · subst h0
    have key : ∀ ν : ℕ → ℝ, (∑' i : ℕ, numTerm ν 0 (i + 1)) / (1 + ∑' i : ℕ, denTerm ν 0 (i + 1))
        = 1 / ν 1 := by
      intro ν
      have e1 : (∑' i : ℕ, numTerm ν 0 (i + 1)) = 1 / ν 1 := by
        rw [tsum_eq_single 0]
        · simp [numTerm, AuxCNC.prodRates_one]
        · intro i hi
          simp [numTerm, hi]
      have e2 : (∑' i : ℕ, denTerm ν 0 (i + 1)) = 0 := by
        simp [denTerm]
      rw [e1, e2]; simp
    rw [key μ, key μ']
    have h1 := hμ 1 le_rfl
    have h2 := hle 1 le_rfl
    have : 1 / μ' 1 ≤ 1 / μ 1 := one_div_le_one_div_of_le h1 h2
    linarith

end Mono

section RC

namespace AuxRC

lemma int_pow (v R : ℝ) (hv : 0 < v) (hR : 0 < R) (m : ℕ) :
    ∫ t in (0:ℝ)..R / v, ((R - v * t) / R) ^ m = R / (v * ((m : ℝ) + 1)) := by
  have hm : (0:ℝ) < (m : ℝ) + 1 := by positivity
  have hderiv : ∀ x ∈ Set.uIcc (0:ℝ) (R / v),
      HasDerivAt (fun t : ℝ => -(R / (v * ((m : ℝ) + 1))) * ((R - v * t) / R) ^ (m + 1))
        (((R - v * x) / R) ^ m) x := by
    intro x _
    have h1 : HasDerivAt (fun t : ℝ => (R - v * t) / R) (-v / R) x := by
      have := ((hasDerivAt_id x).const_mul v).const_sub R |>.div_const R
      simpa using this
    have h2 := (h1.pow (m + 1)).const_mul (-(R / (v * ((m : ℝ) + 1))))
    refine h2.congr_deriv ?_
    have hm' : (m:ℝ) + 1 ≠ 0 := hm.ne'
    have hR' : R ≠ 0 := hR.ne'
    have hv' : v ≠ 0 := hv.ne'
    simp only [Nat.add_sub_cancel]
    push_cast
    field_simp
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv]
  · have : (R - v * (R / v)) / R = 0 := by field_simp; ring
    simp only [this, zero_pow (Nat.succ_ne_zero m), mul_zero, mul_zero, sub_zero]
    simp
    field_simp
    try simp
  · apply Continuous.intervalIntegrable
    fun_prop

lemma int_bounds (v R : ℝ) (hv : 0 < v) (hR : 0 < R) (m : ℕ) (e : ℝ → ℝ) (he : Continuous e)
    (hneg : ∀ t, 0 ≤ t → e t ≤ 0) :
    0 ≤ ∫ t in (0:ℝ)..R / v, ((R - v * t) / R) ^ m * Real.exp (e t) ∧
    ∫ t in (0:ℝ)..R / v, ((R - v * t) / R) ^ m * Real.exp (e t) ≤ R / (v * ((m : ℝ) + 1)) := by
  have hab : (0:ℝ) ≤ R / v := by positivity
  have hbase : ∀ t ∈ Set.Icc (0:ℝ) (R / v), 0 ≤ (R - v * t) / R := by
    intro t ht
    have : v * t ≤ R := by
      have := ht.2
      rw [le_div_iff₀ hv] at this
      linarith
    apply div_nonneg _ hR.le
    linarith
  refine ⟨?_, ?_⟩
  · apply intervalIntegral.integral_nonneg hab
    intro t ht
    exact mul_nonneg (pow_nonneg (hbase t ht) _) (Real.exp_pos _).le
  · rw [← int_pow v R hv hR m]
    apply intervalIntegral.integral_mono_on hab
    · apply Continuous.intervalIntegrable
      have : Continuous (fun t : ℝ => (R - v * t) / R) := by fun_prop
      exact (this.pow m).mul (Real.continuous_exp.comp he)
    · apply Continuous.intervalIntegrable
      have : Continuous (fun t : ℝ => (R - v * t) / R) := by fun_prop
      exact this.pow m
    · intro t ht
      apply mul_le_of_le_one_right (pow_nonneg (hbase t ht) _)
      exact Real.exp_le_one_iff.2 (hneg t ht.1)

end AuxRC

theorem rc_solution (lam d v R : ℝ) (k : ℕ) (hd : 0 < d) (hv : 0 < v) (hR : 0 < R)
    (hk : 1 ≤ k) (hlam0 : 0 ≤ lam) (n : ℕ) (hn : 1 ≤ n) :
    0 < mu1c d v R k n ∧ mu1c d v R k n ≤ muNC lam d v R k n := by
  have hn' : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hk' : (1:ℝ) ≤ k := by exact_mod_cast hk
  have hdv : 0 < d / v := by positivity
  by_cases hnk : n ≤ k
  · -- muNC branch 1
    have hI := AuxRC.int_bounds v R hv hR (k - n + 1)
      (fun t => -(((n : ℝ) - 1) * v ^ 2 * t ^ 2) / (2 * R * d)) (by fun_prop) (by
        intro t _
        apply div_nonpos_of_nonpos_of_nonneg
        · apply neg_nonpos.2
          have : (0:ℝ) ≤ (n:ℝ) - 1 := by linarith
          positivity
        · positivity)
    have hmuNC : muNC lam d v R k n = (n : ℝ) / (d / v + ∫ t in (0 : ℝ)..R / v,
      ((R - v * t) / R) ^ (k - n + 1) * Real.exp (-(((n : ℝ) - 1) * v ^ 2 * t ^ 2) / (2 * R * d))) := by
      simp [muNC, hnk]
    rw [hmuNC]
    have hD : 0 < d / v + ∫ t in (0 : ℝ)..R / v,
      ((R - v * t) / R) ^ (k - n + 1) * Real.exp (-(((n : ℝ) - 1) * v ^ 2 * t ^ 2) / (2 * R * d)) := by
      have := hI.1
      linarith
    rcases Nat.lt_or_eq_of_le hnk with hlt | heq
    · have hc : ((k - n + 1 : ℕ) : ℝ) = (k : ℝ) - n + 1 := by
        rw [Nat.cast_add, Nat.cast_sub hnk]; simp
      have hpos : (0:ℝ) < (k : ℝ) - n + 1 := by
        have : (n:ℝ) ≤ k := by exact_mod_cast hnk
        linarith
      have hmu : mu1c d v R k n = (n : ℝ) / (d / v + R / (v * ((k : ℝ) - n + 1))) := by
        simp [mu1c, hlt]
      rw [hmu]
      have h1 : 0 < d / v + R / (v * ((k : ℝ) - n + 1)) := by positivity
      refine ⟨by positivity, ?_⟩
      apply div_le_div_of_nonneg_left (by positivity) hD
      rw [hc] at hI
      have h2 : R / (v * (((k : ℝ) - n + 1) + 1)) ≤ R / (v * ((k : ℝ) - n + 1)) := by
        apply div_le_div_of_nonneg_left hR.le (by positivity)
        nlinarith
      linarith [hI.2]
    · subst heq
      have hmu : mu1c d v R n n = (n : ℝ) / (d / v + R / (2 * v)) := by
        simp [mu1c]
      rw [hmu]
      refine ⟨by positivity, ?_⟩
      apply div_le_div_of_nonneg_left (by positivity) hD
      have e : n - n + 1 = 1 := by omega
      rw [e] at hI hD ⊢
      have h2 : R / (v * (((1:ℕ):ℝ) + 1)) = R / (2 * v) := by
        norm_num; ring_nf
      have := hI.2
      rw [h2] at this
      linarith
  · have hlt : k < n := by omega
    have hI := AuxRC.int_bounds v R hv hR (n - k)
      (fun t => -(lam * v * t ^ 2) / (2 * R)) (by fun_prop) (by
        intro t _
        apply div_nonpos_of_nonpos_of_nonneg
        · apply neg_nonpos.2
          positivity
        · positivity)
    have hmuNC : muNC lam d v R k n = (k : ℝ) / (d / v + ∫ t in (0 : ℝ)..R / v,
      ((R - v * t) / R) ^ (n - k) * Real.exp (-(lam * v * t ^ 2) / (2 * R))) := by
      simp [muNC, hnk]
    rw [hmuNC]
    have hD : 0 < d / v + ∫ t in (0 : ℝ)..R / v,
      ((R - v * t) / R) ^ (n - k) * Real.exp (-(lam * v * t ^ 2) / (2 * R)) := by
      have := hI.1
      linarith
    have hc : ((n - k : ℕ) : ℝ) = (n : ℝ) - k := by
      rw [Nat.cast_sub hlt.le]
    have hmu : mu1c d v R k n = (k : ℝ) / (d / v + R / (v * ((n : ℝ) - k + 1))) := by
      rw [mu1c, if_neg (by omega), if_neg (by omega)]
    have hpos : (0:ℝ) < (n : ℝ) - k + 1 := by
      have : (k:ℝ) ≤ n := by exact_mod_cast hlt.le
      linarith
    rw [hmu]
    refine ⟨by positivity, ?_⟩
    apply div_le_div_of_nonneg_left (by positivity) hD
    rw [hc] at hI
    linarith [hI.2]

end RC

section T11
open Filter Topology

namespace AuxT11

lemma prodRates_pos (μ : ℕ → ℝ) (hμ : ∀ n, 1 ≤ n → 0 < μ n) (i : ℕ) : 0 < prodRates μ i := by
  unfold prodRates
  apply Finset.prod_pos
  intro j hj
  exact hμ j (Finset.mem_Icc.mp hj).1

lemma prodRates_succ (μ : ℕ → ℝ) (i : ℕ) :
    prodRates μ (i + 1) = prodRates μ i * μ (i + 1) := by
  unfold prodRates
  exact Finset.prod_Icc_succ_top (by omega) _

/-- convergence of the denominator series below the limit rate -/
lemma den_summable (μ : ℕ → ℝ) (hμ : ∀ n, 1 ≤ n → 0 < μ n) (L lam : ℝ) (hL : 0 < L)
    (hlam : 0 < lam) (hlt : lam < L) (hT : Tendsto μ atTop (𝓝 L)) :
    Summable (fun i : ℕ => denTerm μ lam (i + 1)) := by
  have hpos : ∀ i, 0 < denTerm μ lam (i + 1) := fun i => by
    unfold denTerm
    have := prodRates_pos μ hμ (i + 1)
    positivity
  have hT2 : Tendsto (fun i : ℕ => μ (i + 2)) atTop (𝓝 L) := hT.comp (tendsto_add_atTop_nat 2)
  refine summable_of_ratio_test_tendsto_lt_one (l := lam / L) ((div_lt_one hL).2 hlt)
    (Eventually.of_forall (fun i => (hpos i).ne')) ?_
  have : Tendsto (fun i : ℕ => lam / μ (i + 2)) atTop (𝓝 (lam / L)) :=
    tendsto_const_nhds.div hT2 hL.ne'
  refine this.congr (fun i => ?_)
  rw [Real.norm_of_nonneg (hpos (i + 1)).le, Real.norm_of_nonneg (hpos i).le]
  have h1 := prodRates_pos μ hμ (i + 1)
  have h2 := hμ (i + 2) (by omega)
  unfold denTerm
  rw [prodRates_succ μ (i + 1)]
  field_simp
  ring

lemma num_summable (μ : ℕ → ℝ) (hμ : ∀ n, 1 ≤ n → 0 < μ n) (L lam : ℝ) (hL : 0 < L)
    (hlam : 0 < lam) (hlt : lam < L) (hT : Tendsto μ atTop (𝓝 L)) :
    Summable (fun i : ℕ => numTerm μ lam (i + 1)) := by
  have hpos : ∀ i, 0 < numTerm μ lam (i + 1) := fun i => by
    unfold numTerm
    have := prodRates_pos μ hμ (i + 1)
    positivity
  have hT2 : Tendsto (fun i : ℕ => μ (i + 2)) atTop (𝓝 L) := hT.comp (tendsto_add_atTop_nat 2)
  refine summable_of_ratio_test_tendsto_lt_one (l := lam / L) ((div_lt_one hL).2 hlt)
    (Eventually.of_forall (fun i => (hpos i).ne')) ?_
  have h1 : Tendsto (fun i : ℕ => (1 + 1 / ((i : ℝ) + 1)) * (lam / μ (i + 2))) atTop
      (𝓝 ((1 + 0) * (lam / L))) :=
    (tendsto_const_nhds.add tendsto_one_div_add_atTop_nhds_zero_nat).mul
      (tendsto_const_nhds.div hT2 hL.ne')
  simp only [add_zero, one_mul] at h1
  refine h1.congr (fun i => ?_)
  rw [Real.norm_of_nonneg (hpos (i + 1)).le, Real.norm_of_nonneg (hpos i).le]
  have h3 := prodRates_pos μ hμ (i + 1)
  have h2 := hμ (i + 2) (by omega)
  unfold numTerm
  rw [prodRates_succ μ (i + 1)]
  simp only [Nat.add_sub_cancel]
  push_cast
  field_simp
  ring

lemma fw_of_lt (μ : ℕ → ℝ) (hμ : ∀ n, 1 ≤ n → 0 < μ n) (L lam : ℝ) (hL : 0 < L)
    (hlam : 0 ≤ lam) (hlt : lam < L) (hT : Tendsto μ atTop (𝓝 L)) : FiniteWait μ lam := by
  rcases hlam.lt_or_eq with hp | h0
  · exact ⟨num_summable μ hμ L lam hL hp hlt hT, den_summable μ hμ L lam hL hp hlt hT⟩
  · subst h0
    constructor
    · apply summable_of_ne_finset_zero (s := {0})
      intro b hb
      have : b ≠ 0 := by simpa using hb
      simp [numTerm, this]
    · apply summable_of_ne_finset_zero (s := {0})
      intro b hb
      have : b ≠ 0 := by simpa using hb
      simp [denTerm]

lemma not_summable (μ : ℕ → ℝ) (hμ : ∀ n, 1 ≤ n → 0 < μ n) (L lam : ℝ) (hL : 0 < L)
    (hlam : L ≤ lam) (N : ℕ) (hN : ∀ n, N ≤ n → μ n ≤ L) :
    ¬ Summable (fun i : ℕ => denTerm μ lam (i + 1)) := by
  intro hs
  have hlam0 : 0 < lam := lt_of_lt_of_le hL hlam
  have hpos : ∀ i, 0 < denTerm μ lam (i + 1) := fun i => by
    unfold denTerm
    have := prodRates_pos μ hμ (i + 1)
    positivity
  have hmono : ∀ i, N ≤ i → denTerm μ lam (i + 1) ≤ denTerm μ lam (i + 1 + 1) := by
    intro i hi
    have h1 := prodRates_pos μ hμ (i + 1)
    have h2 := hμ (i + 2) (by omega)
    have h3 : μ (i + 2) ≤ lam := le_trans (hN (i + 2) (by omega)) hlam
    unfold denTerm
    rw [prodRates_succ μ (i + 1)]
    rw [pow_succ lam (i + 1), div_le_div_iff₀ h1 (mul_pos h1 h2)]
    have : 0 < lam ^ (i + 1) := pow_pos hlam0 _
    nlinarith [mul_le_mul_of_nonneg_left h3 (mul_pos this h1).le]
  have hge : ∀ i, N ≤ i → denTerm μ lam (N + 1) ≤ denTerm μ lam (i + 1) := by
    intro i hi
    induction i, hi using Nat.le_induction with
    | base => exact le_rfl
    | succ i hi ih => exact ih.trans (hmono i hi)
  have h0 := hs.tendsto_atTop_zero
  have hev := h0.eventually (gt_mem_nhds (hpos N))
  obtain ⟨i, hi1, hi2⟩ := (hev.and (eventually_ge_atTop N)).exists
  exact absurd (hge i hi2) (not_le.2 hi1)

lemma mu1c_eq (d v R : ℝ) (k n : ℕ) (hn : k < n) :
    mu1c d v R k n = (k : ℝ) / (d / v + R / (v * ((n : ℝ) - k + 1))) := by
  rw [mu1c, if_neg (by omega), if_neg (by omega)]

lemma mu1c_pos (d v R : ℝ) (k : ℕ) (hd : 0 < d) (hv : 0 < v) (hR : 0 < R) (hk : 1 ≤ k)
    (n : ℕ) (hn : 1 ≤ n) : 0 < mu1c d v R k n := by
  have hn' : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hk' : (1:ℝ) ≤ k := by exact_mod_cast hk
  unfold mu1c
  split_ifs with h1 h2
  · have : (n:ℝ) + 1 ≤ k := by exact_mod_cast h1
    have : (0:ℝ) < (k : ℝ) - n + 1 := by linarith
    positivity
  · positivity
  · have : (k:ℝ) < n := by exact_mod_cast (by omega : k < n)
    have : (0:ℝ) < (n : ℝ) - k + 1 := by linarith
    positivity

lemma mu1c_tendsto (d v R : ℝ) (k : ℕ) (hd : 0 < d) (hv : 0 < v) (hR : 0 < R) (hk : 1 ≤ k) :
    Tendsto (mu1c d v R k) atTop (𝓝 ((k : ℝ) * v / d)) := by
  have hdv : 0 < d / v := by positivity
  have h1 : Tendsto (fun n : ℕ => (n : ℝ) - k + 1) atTop atTop := by
    have : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
    have := tendsto_atTop_add_const_right atTop (-(k : ℝ) + 1) this
    refine this.congr (fun n => ?_)
    ring
  have h2 : Tendsto (fun n : ℕ => v * ((n : ℝ) - k + 1)) atTop atTop :=
    h1.const_mul_atTop hv
  have h3 : Tendsto (fun n : ℕ => R / (v * ((n : ℝ) - k + 1))) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop h2
  have h4 : Tendsto (fun n : ℕ => (k : ℝ) / (d / v + R / (v * ((n : ℝ) - k + 1)))) atTop
      (𝓝 ((k : ℝ) / (d / v + 0))) :=
    tendsto_const_nhds.div (tendsto_const_nhds.add h3) (by rw [add_zero]; exact hdv.ne')
  have h5 : (k : ℝ) / (d / v + 0) = (k : ℝ) * v / d := by
    rw [add_zero]; field_simp
  rw [h5] at h4
  refine h4.congr' ?_
  filter_upwards [eventually_gt_atTop k] with n hn
  exact (mu1c_eq d v R k n hn).symm

lemma mu1c_le (d v R : ℝ) (k : ℕ) (hd : 0 < d) (hv : 0 < v) (hR : 0 < R) (hk : 1 ≤ k)
    (n : ℕ) (hn : k < n) : mu1c d v R k n ≤ (k : ℝ) * v / d := by
  have hk' : (1:ℝ) ≤ k := by exact_mod_cast hk
  have hnk : (k:ℝ) < n := by exact_mod_cast hn
  have hdv : 0 < d / v := by positivity
  rw [mu1c_eq d v R k n hn]
  have hpos : (0:ℝ) < (n : ℝ) - k + 1 := by linarith
  have h5 : (k : ℝ) * v / d = (k : ℝ) / (d / v) := by field_simp
  rw [h5]
  apply div_le_div_of_nonneg_left (by positivity) hdv
  have : 0 < R / (v * ((n : ℝ) - k + 1)) := by positivity
  linarith

end AuxT11

theorem t11_solution (lam d v R : ℝ) (k : ℕ) (hd : 0 < d) (hv : 0 < v) (hR : 0 < R) (hk : 1 ≤ k)
    (hlam0 : 0 ≤ lam) :
    FiniteWait (mu1c d v R k) lam ↔ lam < k * v / d := by
  have hk' : (1:ℝ) ≤ k := by exact_mod_cast hk
  have hL : 0 < (k : ℝ) * v / d := by positivity
  have hpos := AuxT11.mu1c_pos d v R k hd hv hR hk
  constructor
  · intro h
    by_contra hge
    push_neg at hge
    exact AuxT11.not_summable (mu1c d v R k) hpos _ lam hL hge (k + 1)
      (fun n hn => AuxT11.mu1c_le d v R k hd hv hR hk n (by omega)) h.2
  · intro h
    exact AuxT11.fw_of_lt (mu1c d v R k) hpos _ lam hL hlam0 h
      (AuxT11.mu1c_tendsto d v R k hd hv hR hk)

end T11

theorem solution (lam d v R : ℝ) (k : ℕ) (hd : 0 < d) (hv : 0 < v) (hR : 0 < R) (hk : 1 ≤ k)
    (hlam0 : 0 ≤ lam) (hlam : lam < k * v / d) :
    FiniteWait (mu1c d v R k) lam ∧ FiniteWait (muNC lam d v R k) lam ∧
      Wnc lam d v R k ≤ W1c lam d v R k := by
  have h1 : FiniteWait (mu1c d v R k) lam := (t11_solution lam d v R k hd hv hR hk hlam0).2 hlam
  have hpos : ∀ n, 1 ≤ n → 0 < mu1c d v R k n := fun n hn =>
    (rc_solution lam d v R k hd hv hR hk hlam0 n hn).1
  have hle : ∀ n, 1 ≤ n → mu1c d v R k n ≤ muNC lam d v R k n := fun n hn =>
    (rc_solution lam d v R k hd hv hR hk hlam0 n hn).2
  obtain ⟨h2, h3⟩ := mono_solution (mu1c d v R k) (muNC lam d v R k) lam d v hpos hle hlam0 h1
  exact ⟨h1, h2, h3⟩
