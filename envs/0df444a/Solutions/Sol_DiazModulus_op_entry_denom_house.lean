-- Prove2me | solution 1 for DiazModulus.op_entry_denom_house
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-29T06:21:21.929984+00:00
-- url     : https://prove2.me/submissions/5d4a871f-0e30-4b45-8bfc-e108734e1eef

import Mathlib
import Definitions.Def_DiazModulus
import Theorems.Thm_Transcendence_exists_denom_house_monomial_le

open Complex ComplexConjugate

/-! # Denominators and houses of the interpolation entries

All data (the coordinates of `w`, of `u`, the `a j i` and their inverses) form one finite family
`θ`; `Transcendence.exists_denom_house_monomial_le` gives a common denominator `b` and a bound
`H₀` with `b θ` integral of house `≤ H₀`. Write `Q x n B` for "`bⁿ x` is integral with house
`≤ H₀ⁿ B`"; it is stable under sums (same `n`), products (adding `n`), integer multiples and
raising `n`. By induction on the list of operators, every coefficient of `Op⋯Op X^τ` satisfies
`Q · r ((|ι₀|+1)(|τ|+|t|+1))^r`, and its support lies below `τ` (`MvPolynomial.coeff_pderiv`).
Evaluating at `Σ sⱼuⱼ` costs `Q · |ν| (|s|+1)^|ν|` per monomial, and at most `2^|τ|` monomials.
The factor `Π_i (Π_j a_ji^{s_j})^{t_i} = Π a_ji^{s_j t_i}` satisfies `Q · (|t||s|) 1`.
The constants `2^|τ|` and `(|ι₀|+1)^r` are absorbed into `H = 2 H₀ (|ι₀|+1)`. -/

set_option linter.unusedSectionVars false

namespace C14_A8
open DiazModulus

variable {K : Type*} [Field K] [NumberField K]

/-- `bⁿ x` is integral with house at most `H₀ⁿ B`. -/
def Q (b : K) (H₀ : ℝ) (x : K) (n : ℕ) (B : ℝ) : Prop :=
  IsIntegral ℤ (b ^ n * x) ∧ NumberField.house (b ^ n * x) ≤ H₀ ^ n * B

variable {b : K} {H₀ : ℝ}

lemma Q_zero (hH : 0 ≤ H₀) {B : ℝ} (hB : 0 ≤ B) (n : ℕ) : Q b H₀ 0 n B := by
  refine ⟨by simpa using isIntegral_zero, ?_⟩
  simp only [mul_zero]
  have : NumberField.house (0 : K) = 0 := by simpa using NumberField.house_intCast (K := K) 0
  rw [this]; positivity

lemma Q_one : Q b H₀ 1 0 1 := by
  refine ⟨by simpa using isIntegral_one, ?_⟩
  simpa using le_of_eq (NumberField.house_intCast (K := K) 1)

lemma Q_mono (hb : IsIntegral ℤ b) (hbH : NumberField.house b ≤ H₀) {x : K} {n m : ℕ} {B B' : ℝ}
    (h : Q b H₀ x n B) (hnm : n ≤ m) (hBB : B ≤ B') : Q b H₀ x m B' := by
  have e : b ^ m * x = b ^ (m - n) * (b ^ n * x) := by
    rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel hnm]
  have h0 : 0 ≤ NumberField.house b := NumberField.house_nonneg _
  have hp : NumberField.house (b ^ (m - n)) ≤ H₀ ^ (m - n) :=
    (NumberField.house_pow_le _ _).trans (pow_le_pow_left₀ h0 hbH _)
  refine ⟨e ▸ (hb.pow _).mul h.1, ?_⟩
  rw [e]
  calc NumberField.house (b ^ (m - n) * (b ^ n * x))
      ≤ NumberField.house (b ^ (m - n)) * NumberField.house (b ^ n * x) :=
        NumberField.house_mul_le _ _
    _ ≤ H₀ ^ (m - n) * (H₀ ^ n * B) :=
        mul_le_mul hp h.2 (NumberField.house_nonneg _) ((NumberField.house_nonneg _).trans hp)
    _ ≤ H₀ ^ m * B' := by
        rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel hnm]
        exact mul_le_mul_of_nonneg_left hBB (pow_nonneg (h0.trans hbH) _)

lemma Q_add {x y : K} {n : ℕ} {B B' : ℝ} (h : Q b H₀ x n B) (h' : Q b H₀ y n B') :
    Q b H₀ (x + y) n (B + B') := by
  refine ⟨by rw [mul_add]; exact h.1.add h'.1, ?_⟩
  rw [mul_add, mul_add]
  exact (NumberField.house_add_le _ _).trans (add_le_add h.2 h'.2)

lemma Q_mul {x y : K} {n m : ℕ} {B B' : ℝ} (h : Q b H₀ x n B) (h' : Q b H₀ y m B') :
    Q b H₀ (x * y) (n + m) (B * B') := by
  have e : b ^ (n + m) * (x * y) = (b ^ n * x) * (b ^ m * y) := by rw [pow_add]; ring
  refine ⟨e ▸ h.1.mul h'.1, ?_⟩
  rw [e]
  calc _ ≤ NumberField.house (b ^ n * x) * NumberField.house (b ^ m * y) :=
        NumberField.house_mul_le _ _
    _ ≤ (H₀ ^ n * B) * (H₀ ^ m * B') :=
        mul_le_mul h.2 h'.2 (NumberField.house_nonneg _) ((NumberField.house_nonneg _).trans h.2)
    _ = H₀ ^ (n + m) * (B * B') := by rw [pow_add]; ring

lemma Q_int_mul {x : K} {n : ℕ} {B : ℝ} (h : Q b H₀ x n B) (z : ℤ) :
    Q b H₀ ((z : K) * x) n (z.natAbs * B) := by
  have e : b ^ n * ((z : K) * x) = (z : K) * (b ^ n * x) := by ring
  refine ⟨e ▸ (isIntegral_intCast z).mul h.1, ?_⟩
  rw [e]
  calc _ ≤ NumberField.house (z : K) * NumberField.house (b ^ n * x) :=
        NumberField.house_mul_le _ _
    _ ≤ z.natAbs * (H₀ ^ n * B) := by
        rw [NumberField.house_intCast, Int.cast_abs, Nat.cast_natAbs, Int.cast_abs]
        exact mul_le_mul_of_nonneg_left h.2 (abs_nonneg _)
    _ = H₀ ^ n * (z.natAbs * B) := by ring

lemma Q_sum (hH : 0 ≤ H₀) {ι : Type*} (s : Finset ι) (f : ι → K) (n : ℕ) (B : ι → ℝ)
    (h : ∀ i ∈ s, Q b H₀ (f i) n (B i)) : Q b H₀ (∑ i ∈ s, f i) n (∑ i ∈ s, B i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using Q_zero hH le_rfl n
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact Q_add (h a (Finset.mem_insert_self _ _))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

lemma Q_prod {ι : Type*} (s : Finset ι) (f : ι → K) (n : ι → ℕ) (B : ι → ℝ)
    (h : ∀ i ∈ s, Q b H₀ (f i) (n i) (B i)) :
    Q b H₀ (∏ i ∈ s, f i) (∑ i ∈ s, n i) (∏ i ∈ s, B i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using Q_one
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha, Finset.prod_insert ha]
    exact Q_mul (h a (Finset.mem_insert_self _ _))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

lemma Q_pow {x : K} {n : ℕ} {B : ℝ} (h : Q b H₀ x n B) (k : ℕ) :
    Q b H₀ (x ^ k) (n * k) (B ^ k) := by
  rw [mul_comm]
  simpa [Finset.prod_const, Finset.sum_const] using
    Q_prod (Finset.range k) (fun _ => x) (fun _ => n) (fun _ => B) (fun _ _ => h)

lemma Q_zpow {x : K} (h : Q b H₀ x 1 1) (h' : Q b H₀ x⁻¹ 1 1) (m : ℤ) :
    Q b H₀ (x ^ m) m.natAbs 1 := by
  obtain ⟨k, rfl | rfl⟩ := Int.eq_nat_or_neg m
  · rw [zpow_natCast]; simpa using Q_pow h k
  · rw [zpow_neg, zpow_natCast, ← inv_pow]; simpa using Q_pow h' k

lemma gen_of_spec {ι : Type*} [Fintype ι] [DecidableEq ι] (θ : ι → K)
    (hspec : ∀ (e : ι → ℕ) (E : ℕ), ∑ i, e i ≤ E → IsIntegral ℤ (b ^ E * ∏ i, θ i ^ e i) ∧
      NumberField.house (b ^ E * ∏ i, θ i ^ e i) ≤ H₀ ^ E) (i : ι) : Q b H₀ (θ i) 1 1 := by
  have := hspec (fun j => if j = i then 1 else 0) 1 (by simp)
  simpa [Q, pow_ite, Finset.prod_ite_eq'] using this

lemma house_le_of_spec {ι : Type*} [Fintype ι] (θ : ι → K)
    (hspec : ∀ (e : ι → ℕ) (E : ℕ), ∑ i, e i ≤ E → IsIntegral ℤ (b ^ E * ∏ i, θ i ^ e i) ∧
      NumberField.house (b ^ E * ∏ i, θ i ^ e i) ≤ H₀ ^ E) : NumberField.house b ≤ H₀ := by
  simpa using (hspec 0 1 (by simp)).2

section poly
variable {ι₀ : Type} [Fintype ι₀] [DecidableEq ι₀]

lemma op_coeff (c1 : ι₀ → K) (c : K) (P : MvPolynomial ι₀ K) (ν : ι₀ →₀ ℕ) :
    ((∑ h, c1 h • (MvPolynomial.pderiv h).toLinearMap + c • LinearMap.id :
      Module.End K (MvPolynomial ι₀ K)) P).coeff ν
      = ∑ h, c1 h * (P.coeff (ν + Finsupp.single h 1) * ((ν h : K) + 1))
        + c * P.coeff ν := by
  simp [LinearMap.add_apply, MvPolynomial.coeff_sum, MvPolynomial.coeff_pderiv]

lemma prod_X_pow_eq (τ : ι₀ → ℕ) :
    (∏ h, MvPolynomial.X h ^ τ h : MvPolynomial ι₀ K)
      = MvPolynomial.monomial (Finsupp.equivFunOnFinite.symm τ) 1 := by
  rw [MvPolynomial.monomial_eq, MvPolynomial.C_1, one_mul, Finsupp.prod_fintype _ _ (by simp)]
  simp

lemma poly_inv (hb : IsIntegral ℤ b) (hbH : NumberField.house b ≤ H₀) (τ : ι₀ → ℕ) {T : ℝ}
    (hT : 0 ≤ T) (l : List (Module.End K (MvPolynomial ι₀ K)))
    (hl : ∀ op ∈ l, ∃ c1 : ι₀ → K, ∃ c : K, (∀ h, Q b H₀ (c1 h) 1 1) ∧ Q b H₀ c 1 T ∧
      op = ∑ h, c1 h • (MvPolynomial.pderiv h).toLinearMap + c • LinearMap.id) :
    (∀ ν, Q b H₀ ((l.prod (∏ h, MvPolynomial.X h ^ τ h)).coeff ν) l.length
        (((Fintype.card ι₀ + 1 : ℝ) * ((∑ h, τ h : ℕ) + T + 1)) ^ l.length)) ∧
      (∀ ν, (l.prod (∏ h, MvPolynomial.X h ^ τ h)).coeff ν ≠ 0 → ∀ h, ν h ≤ τ h) := by
  have hH : 0 ≤ H₀ := (NumberField.house_nonneg b).trans hbH
  set S : ℝ := ((∑ h, τ h : ℕ) : ℝ)
  have hS : 0 ≤ S := Nat.cast_nonneg _
  induction l with
  | nil =>
    simp only [List.prod_nil, Module.End.one_apply, List.length_nil, pow_zero, prod_X_pow_eq,
      MvPolynomial.coeff_monomial]
    refine ⟨fun ν => ?_, fun ν hν h => ?_⟩
    · split_ifs
      · exact Q_one
      · exact Q_zero hH zero_le_one 0
    · split_ifs at hν with e
      · subst e; simp
      · exact absurd rfl hν
  | cons op l ih =>
    obtain ⟨c1, c, hc1, hc, rfl⟩ := hl op (List.mem_cons_self ..)
    obtain ⟨ihQ, ihS⟩ := ih fun o ho => hl o (List.mem_cons_of_mem _ ho)
    set B := ((Fintype.card ι₀ + 1 : ℝ) * (S + T + 1)) ^ l.length
    have hB : 0 ≤ B := by positivity
    simp only [List.prod_cons, Module.End.mul_apply, List.length_cons]
    refine ⟨fun ν => ?_, fun ν hν => ?_⟩
    · rw [op_coeff]
      have hterm : ∀ h, Q b H₀ ((l.prod (∏ h, MvPolynomial.X h ^ τ h)).coeff
          (ν + Finsupp.single h 1) * ((ν h : K) + 1)) l.length (S * B) := by
        intro h
        by_cases h0 : (l.prod (∏ h, MvPolynomial.X h ^ τ h)).coeff
            (ν + Finsupp.single h 1) = 0
        · rw [h0, zero_mul]; exact Q_zero hH (by positivity) _
        have hle : ν h + 1 ≤ ∑ h, τ h := by
          have := ihS _ h0 h
          simp only [Finsupp.coe_add, Pi.add_apply, Finsupp.single_eq_same] at this
          exact this.trans (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ h))
        have e : (l.prod (∏ h, MvPolynomial.X h ^ τ h)).coeff (ν + Finsupp.single h 1)
              * ((ν h : K) + 1)
            = (((ν h + 1 : ℕ) : ℤ) : K) * (l.prod (∏ h, MvPolynomial.X h ^ τ h)).coeff
              (ν + Finsupp.single h 1) := by push_cast; ring
        rw [e]
        refine Q_mono hb hbH (Q_int_mul (ihQ _) _) le_rfl ?_
        rw [Int.natAbs_natCast]
        exact mul_le_mul_of_nonneg_right (by simp only [S]; exact_mod_cast hle) hB
      have h1 := Q_sum hH Finset.univ _ (1 + l.length) _ fun h _ => Q_mul (hc1 h) (hterm h)
      have h2 := Q_add h1 (Q_mul hc (ihQ ν))
      refine Q_mono hb hbH h2 (by omega) ?_
      simp only [one_mul, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      have hc0 : (0 : ℝ) ≤ Fintype.card ι₀ := Nat.cast_nonneg _
      rw [pow_succ]
      nlinarith [mul_nonneg hc0 hS, mul_nonneg hc0 hT, mul_nonneg hB (mul_nonneg hc0 hS),
        mul_nonneg hB (mul_nonneg hc0 hT), mul_nonneg hB hc0, mul_nonneg hB hS, mul_nonneg hB hT]
    · intro h0
      by_contra hne
      apply hν
      rw [op_coeff]
      have hz : ∀ μ : ι₀ →₀ ℕ, ν h0 ≤ μ h0 →
          (l.prod (∏ h, MvPolynomial.X h ^ τ h)).coeff μ = 0 := by
        intro μ hμ
        by_contra hc'
        exact hne (hμ.trans (ihS μ hc' h0))
      rw [hz ν le_rfl, mul_zero, add_zero]
      refine Finset.sum_eq_zero fun h _ => ?_
      rw [hz _ (by simp), zero_mul, mul_zero]

lemma card_support_le (P : MvPolynomial ι₀ K) (τ : ι₀ → ℕ)
    (hP : ∀ ν, P.coeff ν ≠ 0 → ∀ h, ν h ≤ τ h) :
    P.support.card ≤ 2 ^ (∑ h, τ h) := by
  calc P.support.card ≤ (Fintype.piFinset fun h => Finset.range (τ h + 1)).card := by
        refine Finset.card_le_card_of_injOn (fun ν => ⇑ν) (fun ν hν => ?_)
          (fun x _ y _ e => DFunLike.coe_injective e)
        simp only [Finset.mem_coe, Fintype.mem_piFinset, Finset.mem_range]
        exact fun h => Nat.lt_succ_of_le (hP ν (MvPolynomial.mem_support_iff.mp hν) h)
    _ = ∏ h, (τ h + 1) := by simp [Fintype.card_piFinset]
    _ ≤ ∏ h, 2 ^ τ h := Finset.prod_le_prod' fun h _ => Nat.lt_two_pow_self
    _ = 2 ^ (∑ h, τ h) := Finset.prod_pow_eq_pow_sum _ _ _

lemma eval_Q (hb : IsIntegral ℤ b) (hbH : NumberField.house b ≤ H₀) (τ : ι₀ → ℕ)
    (P : MvPolynomial ι₀ K) {n : ℕ} {B V : ℝ} (hB : 0 ≤ B) (hV : 0 ≤ V)
    (hQ : ∀ ν, Q b H₀ (P.coeff ν) n B)
    (hP : ∀ ν, P.coeff ν ≠ 0 → ∀ h, ν h ≤ τ h)
    (p : ι₀ → K) (hp : ∀ h, Q b H₀ (p h) 1 V) :
    Q b H₀ (MvPolynomial.eval p P) (n + ∑ h, τ h) (2 ^ (∑ h, τ h) * B * (V + 1) ^ (∑ h, τ h)) := by
  have hH : 0 ≤ H₀ := (NumberField.house_nonneg b).trans hbH
  rw [MvPolynomial.eval_eq']
  have hterm : ∀ d ∈ P.support, Q b H₀ (P.coeff d * ∏ i, p i ^ d i)
      (n + ∑ h, τ h) (B * (V + 1) ^ (∑ h, τ h)) := by
    intro d hd
    have hd' := hP d (MvPolynomial.mem_support_iff.mp hd)
    have h1 := Q_mul (hQ d) (Q_prod Finset.univ _ _ _ fun i _ => Q_pow (hp i) (d i))
    refine Q_mono hb hbH h1 ?_ ?_
    · simpa using Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => hd' i
    · rw [Finset.prod_pow_eq_pow_sum]
      refine mul_le_mul_of_nonneg_left ?_ hB
      calc V ^ (∑ i, d i) ≤ (V + 1) ^ (∑ i, d i) := pow_le_pow_left₀ hV (by linarith) _
        _ ≤ (V + 1) ^ (∑ h, τ h) :=
          pow_le_pow_right₀ (by linarith) (Finset.sum_le_sum fun i _ => hd' i)
  refine Q_mono hb hbH (Q_sum hH _ _ _ _ hterm) le_rfl ?_
  rw [Finset.sum_const, nsmul_eq_mul, mul_assoc]
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast card_support_le P τ hP) (by positivity)

end poly

end C14_A8

open DiazModulus C14_A8 in
theorem solution {K : Type*} [Field K] [NumberField K] {ι₀ ι₁ κ₀ κ₁ : Type} [Fintype ι₀] [Fintype ι₁]
    [Fintype κ₀] [Fintype κ₁] [DecidableEq ι₀]
    (w : κ₀ → (ι₀ → K) × (ι₁ → K)) (u : κ₁ → ι₀ → K) (a : κ₁ → ι₁ → K) :
    ∃ b : K, b ≠ 0 ∧ IsIntegral ℤ b ∧ ∃ H : ℝ, 1 ≤ H ∧
      ∀ (r : ℕ) (κ : Fin r → κ₀) (s : κ₁ → ℤ) (τ : ι₀ → ℕ) (t : ι₁ → ℤ),
        IsIntegral ℤ (b ^ (r + ∑ h, τ h + (∑ i, (t i).natAbs) * ∑ j, (s j).natAbs) *
            (MvPolynomial.eval (∑ j, (s j : K) • u j) ((List.ofFn fun k : Fin r =>
            ((∑ h, (w (κ k)).1 h • (MvPolynomial.pderiv h).toLinearMap
              + (∑ i, (w (κ k)).2 i * (t i : K)) • LinearMap.id :
                Module.End K (MvPolynomial ι₀ K)))).prod
              (∏ h, MvPolynomial.X h ^ τ h)) * ∏ i, (∏ j, a j i ^ s j) ^ t i)) ∧
        NumberField.house (b ^ (r + ∑ h, τ h + (∑ i, (t i).natAbs) * ∑ j, (s j).natAbs) *
            (MvPolynomial.eval (∑ j, (s j : K) • u j) ((List.ofFn fun k : Fin r =>
            ((∑ h, (w (κ k)).1 h • (MvPolynomial.pderiv h).toLinearMap
              + (∑ i, (w (κ k)).2 i * (t i : K)) • LinearMap.id :
                Module.End K (MvPolynomial ι₀ K)))).prod
              (∏ h, MvPolynomial.X h ^ τ h)) * ∏ i, (∏ j, a j i ^ s j) ^ t i))
          ≤ H ^ (r + ∑ h, τ h + (∑ i, (t i).natAbs) * ∑ j, (s j).natAbs)
            * ((∑ h, τ h : ℕ) + (∑ i, (t i).natAbs : ℕ) + 1 : ℝ) ^ r
            * ((∑ j, (s j).natAbs : ℕ) + 1 : ℝ) ^ (∑ h, τ h) := by
  classical
  let θ : (κ₀ × ι₀) ⊕ (κ₀ × ι₁) ⊕ (κ₁ × ι₀) ⊕ (κ₁ × ι₁) ⊕ (κ₁ × ι₁) → K :=
    Sum.elim (fun p => (w p.1).1 p.2) (Sum.elim (fun p => (w p.1).2 p.2)
      (Sum.elim (fun p => u p.1 p.2) (Sum.elim (fun p => a p.1 p.2) (fun p => (a p.1 p.2)⁻¹))))
  obtain ⟨b, hb0, hb, H₀, hH₀, hspec⟩ := Transcendence.exists_denom_house_monomial_le θ
  have hgen : ∀ i, Q b H₀ (θ i) 1 1 := gen_of_spec θ hspec
  have hbH : NumberField.house b ≤ H₀ := house_le_of_spec θ hspec
  have hH : 0 ≤ H₀ := by linarith
  set A : ℝ := (Fintype.card ι₀ + 1 : ℝ)
  have hA : 1 ≤ A := by simp [A]
  refine ⟨b, hb0, hb, H₀ * 2 * A, by nlinarith, ?_⟩
  intro r κ s τ t
  set T : ℝ := ((∑ i, (t i).natAbs : ℕ) : ℝ)
  set V : ℝ := ((∑ j, (s j).natAbs : ℕ) : ℝ)
  set E := r + ∑ h, τ h + (∑ i, (t i).natAbs) * ∑ j, (s j).natAbs
  -- the operator part
  have hl : ∀ op ∈ (List.ofFn fun k : Fin r =>
      ((∑ h, (w (κ k)).1 h • (MvPolynomial.pderiv h).toLinearMap
        + (∑ i, (w (κ k)).2 i * (t i : K)) • LinearMap.id : Module.End K (MvPolynomial ι₀ K)))),
      ∃ c1 : ι₀ → K, ∃ c : K, (∀ h, Q b H₀ (c1 h) 1 1) ∧ Q b H₀ c 1 T ∧
        op = ∑ h, c1 h • (MvPolynomial.pderiv h).toLinearMap + c • LinearMap.id := by
    intro op hop
    obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hop
    refine ⟨_, _, fun h => hgen (Sum.inl (κ k, h)), ?_, rfl⟩
    have := Q_sum hH Finset.univ (fun i => ((t i : ℤ) : K) * (w (κ k)).2 i) 1 _
      fun i _ => Q_int_mul (hgen (Sum.inr (Sum.inl (κ k, i)))) (t i)
    simp only [mul_one] at this
    have h' : Q b H₀ (∑ i, (w (κ k)).2 i * (t i : K)) 1 (∑ i, ((t i).natAbs : ℝ)) := by
      simpa only [mul_comm] using this
    exact Q_mono hb hbH h' le_rfl (by simp only [T]; push_cast; exact le_rfl)
  obtain ⟨hQ, hS⟩ := poly_inv hb hbH τ (Nat.cast_nonneg _) _ hl
  rw [List.length_ofFn] at hQ
  have hp : ∀ h, Q b H₀ ((∑ j, (s j : K) • u j) h) 1 V := by
    intro h
    have := Q_sum hH Finset.univ (fun j => ((s j : ℤ) : K) * u j h) 1 _
      fun j _ => Q_int_mul (hgen (Sum.inr (Sum.inr (Sum.inl (j, h))))) (s j)
    simp only [mul_one] at this
    have h' : Q b H₀ ((∑ j, (s j : K) • u j) h) 1 (∑ j, ((s j).natAbs : ℝ)) := by
      simpa [Finset.sum_apply] using this
    exact Q_mono hb hbH h' le_rfl (by simp only [V]; push_cast; exact le_rfl)
  have hev := eval_Q hb hbH τ _ (by positivity) (Nat.cast_nonneg _) hQ hS _ hp
  -- the exponential part
  have hz : Q b H₀ (∏ i, (∏ j, a j i ^ s j) ^ t i)
      ((∑ i, (t i).natAbs) * ∑ j, (s j).natAbs) 1 := by
    have e : ∀ i, (∏ j, a j i ^ s j) ^ t i = ∏ j, a j i ^ (s j * t i) := by
      intro i; rw [← Finset.prod_zpow]; simp only [zpow_mul]
    simp only [e]
    have := Q_prod Finset.univ _ _ _ fun i _ => Q_prod Finset.univ _ _ _ fun j _ =>
      Q_zpow (hgen (Sum.inr (Sum.inr (Sum.inr (Sum.inl (j, i))))))
        (hgen (Sum.inr (Sum.inr (Sum.inr (Sum.inr (j, i)))))) (s j * t i)
    simp only [Finset.prod_const_one] at this
    refine Q_mono hb hbH this (le_of_eq ?_) le_rfl
    simp only [Int.natAbs_mul, Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => mul_comm _ _
  have hall := Q_mono hb hbH (Q_mul hev hz) le_rfl le_rfl
  refine ⟨hall.1, hall.2.trans ?_⟩
  have hE1 : ∑ h, τ h ≤ E := by simp only [E]; omega
  have hE2 : r ≤ E := by simp only [E]; omega
  have h2 : (2 : ℝ) ^ (∑ h, τ h) ≤ 2 ^ E := pow_le_pow_right₀ (by norm_num) hE1
  have h3 : A ^ r ≤ A ^ E := pow_le_pow_right₀ hA hE2
  have hX : ((∑ h, τ h : ℕ) + T + 1 : ℝ) = ((∑ h, τ h : ℕ) + (∑ i, (t i).natAbs : ℕ) + 1 : ℝ) := rfl
  rw [mul_one, mul_pow, mul_pow, mul_pow, ← hX]
  have : (0 : ℝ) ≤ (V + 1) ^ (∑ h, τ h) * ((∑ h, τ h : ℕ) + T + 1 : ℝ) ^ r := by positivity
  calc H₀ ^ E * (2 ^ (∑ h, τ h) * (A ^ r * ((∑ h, τ h : ℕ) + T + 1 : ℝ) ^ r) * (V + 1) ^ (∑ h, τ h))
      = H₀ ^ E * (2 ^ (∑ h, τ h) * A ^ r) * ((V + 1) ^ (∑ h, τ h) * ((∑ h, τ h : ℕ) + T + 1 : ℝ) ^ r) := by ring
    _ ≤ H₀ ^ E * (2 ^ E * A ^ E) * ((V + 1) ^ (∑ h, τ h) * ((∑ h, τ h : ℕ) + T + 1 : ℝ) ^ r) := by
        gcongr
    _ = _ := by ring
