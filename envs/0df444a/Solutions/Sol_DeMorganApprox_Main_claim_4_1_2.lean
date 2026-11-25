-- Prove2me | solution 1 for DeMorganApprox.Main.claim_4_1_2
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-25T17:14:24.824833+00:00
-- url     : https://prove2.me/submissions/5f907c01-6235-49be-aaa6-c4d1ebc0c158

import Definitions.Def_DeMorganApprox_Main_Extraction

open DeMorganApprox.Main Polynomial Polynomial.Chebyshev

private noncomputable def mass (P : Polynomial ℝ) := P.sum fun _ t => |t|

private lemma mass_nonneg (P : Polynomial ℝ) : 0 ≤ mass P :=
  Finset.sum_nonneg fun _ _ => abs_nonneg _

private lemma mass_add (P Q : Polynomial ℝ) : mass (P + Q) ≤ mass P + mass Q := by
  let U := P.support ∪ Q.support
  have h (R : Polynomial ℝ) (hR : R.support ⊆ U) :
      mass R = ∑ i ∈ U, |R.coeff i| := sum_eq_of_subset _ (fun _ => abs_zero) hR
  rw [h _ support_add, h _ Finset.subset_union_left, h _ Finset.subset_union_right,
    ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun i _ => by simpa using abs_add_le (P.coeff i) (Q.coeff i)

private lemma mass_sub (P Q : Polynomial ℝ) : mass (P - Q) ≤ mass P + mass Q := by
  simpa [sub_eq_add_neg, mass, Polynomial.sum] using mass_add P (-Q)

private lemma mass_sum {α : Type} (s : Finset α) (f : α → Polynomial ℝ) :
    mass (∑ i ∈ s, f i) ≤ ∑ i ∈ s, mass (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [mass]
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact (mass_add ..).trans (add_le_add (le_refl _) ih)

private lemma mass_mul (P Q : Polynomial ℝ) : mass (P * Q) ≤ mass P * mass Q := by
  rw [mul_eq_sum_sum]
  refine (mass_sum _ _).trans ?_
  unfold Polynomial.sum
  calc
    _ ≤ _ := Finset.sum_le_sum fun i _ => mass_sum _ _
    _ = _ := by
      have hm (n : ℕ) (a : ℝ) : mass (monomial n a) = |a| := by simp [mass]
      simp only [hm, abs_mul]
      rw [mass, mass, Polynomial.sum_def, Polynomial.sum_def, Finset.sum_mul]
      simp only [Finset.mul_sum]

private lemma mass_C (a : ℝ) : mass (C a) = |a| := by simp [mass]
private lemma mass_one : mass 1 = 1 := by simpa using mass_C 1
private lemma mass_X : mass X = 1 := by simp [mass]

private lemma mass_T_comp (A : Polynomial ℝ) (hA : mass A ≤ 7) (d : ℕ) :
    mass ((T ℝ (d : ℤ)).comp A) ≤ 16 ^ d := by
  induction d using Nat.twoStepInduction with
  | zero => simp [mass_one]
  | one => simpa using hA.trans (by norm_num : (7:ℝ) ≤ 16)
  | more n h₀ h₁ =>
    push_cast
    rw [T_add_two, sub_comp, mul_comp, mul_comp, X_comp]
    have htwo : mass ((2 : Polynomial ℝ).comp A) = 2 := by
      rw [show (2 : Polynomial ℝ) = C (2:ℝ) by exact (map_ofNat (Polynomial.C : ℝ →+* Polynomial ℝ) 2).symm, C_comp, mass_C]; norm_num
    have hmul : mass ((2 : Polynomial ℝ).comp A * A) ≤ 14 :=
      (mass_mul ..).trans (by rw [htwo]; linarith)
    refine (mass_sub ..).trans ((add_le_add ((mass_mul ..).trans
      (mul_le_mul hmul h₁ (mass_nonneg _) (by norm_num))) h₀).trans ?_)
    simp only [pow_succ]
    nlinarith [pow_nonneg (by norm_num : (0:ℝ) ≤ 16) n]

private lemma mass_arg {e : ℝ} (he : 0 < e) (he' : e ≤ 1/2) : mass (chebArg e) ≤ 7 := by
  have hsq : e^2 ≤ 1/4 := by nlinarith [mul_nonneg (by linarith : 0 ≤ 1/2 - e) (by linarith : 0 ≤ 1/2 + e)]
  have hd : 0 < 1-e^2 := by linarith
  have h₁ : 1+2*e^2/(1-e^2) ≤ 3 := by
    have := (div_le_iff₀ hd).mpr (by linarith : 2*e^2 ≤ 2*(1-e^2)); linarith
  have h₂ : 2/(1-e^2) ≤ 4 := (div_le_iff₀ hd).mpr (by linarith)
  have hx : mass (X^2) ≤ 1 := by
    simpa [pow_two, mass_X] using mass_mul X X
  unfold chebArg
  refine (mass_sub ..).trans ?_
  rw [mass_C, abs_of_nonneg (by positivity)]
  refine (add_le_add h₁ ((mass_mul ..).trans ?_)).trans (by norm_num : (3:ℝ)+4*1≤7)
  apply mul_le_mul _ hx (mass_nonneg _) (by norm_num)
  rw [mass_C, abs_of_pos (by positivity)]
  exact h₂

theorem solution (cnorm ccheb : ℝ) (hcnorm : 1 ≤ cnorm) (hccheb : 0 < ccheb) :
    ∃ K : ℝ, ∀ S : ℝ, 1 ≤ S →
      ∑ j ∈ Finset.range
          ((chebFilterSq (filterEps cnorm S) (filterDeg ccheb (filterEps cnorm S))).natDegree + 1),
        |(chebFilterSq (filterEps cnorm S) (filterDeg ccheb (filterEps cnorm S))).coeff j| ≤
        (2 : ℝ) ^ (K * S) := by
  refine ⟨8*(1000*ccheb*cnorm + 1), ?_⟩
  intro S hS
  let e := filterEps cnorm S
  let d := filterDeg ccheb e
  have hpos : 0 < e := by dsimp [e, filterEps]; positivity
  have hprod : 1 ≤ cnorm*S := one_le_mul_of_one_le_of_one_le hcnorm hS
  have hsmall : e ≤ 1/2 := by
    dsimp [e, filterEps]
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith
  have he2 : e^2 < 1 := by nlinarith [mul_nonneg (by linarith : 0 ≤ 1/2 - e) (by linarith : 0 ≤ 1/2 + e)]
  let a := 1+2*e^2/(1-e^2)
  have ha : 1 ≤ a := by
    dsimp [a]
    have hden : 0 < 1-e^2 := by linarith
    exact le_add_of_nonneg_right (by positivity)
  have hD := one_le_eval_T_real (d:ℤ) ha
  have hN : mass (C (((T ℝ (d:ℤ)).eval a)⁻¹)) ≤ 1 := by
    rw [mass_C, abs_of_pos (by positivity)]
    exact inv_le_one_of_one_le₀ hD
  have hφ : mass (chebFilter e d) ≤ 16 ^ d := by
    exact (mass_mul ..).trans ((mul_le_mul hN (mass_T_comp _ (mass_arg hpos hsmall) d)
      (mass_nonneg _) zero_le_one).trans_eq (one_mul _))
  have hΨ : mass (chebFilterSq e d) ≤ (16 ^ d)^2 := by
    unfold chebFilterSq
    rw [pow_two, pow_two]
    exact (mass_mul ..).trans (mul_le_mul hφ hφ (mass_nonneg _) (by positivity))
  have hdeg : (d : ℝ) ≤ (1000*ccheb*cnorm + 1)*S := by
    have hlt : (d:ℝ) < ccheb/e+1 := Nat.ceil_lt_add_one (by positivity)
    dsimp [e,filterEps] at hlt
    rw [div_div_eq_mul_div, div_one] at hlt
    nlinarith
  change ∑ j ∈ Finset.range ((chebFilterSq e d).natDegree + 1),
    |(chebFilterSq e d).coeff j| ≤ _
  rw [← (chebFilterSq e d).sum_over_range (f := fun _ t => |t|) (fun _ => abs_zero)]
  refine hΨ.trans ?_
  calc
    (((16:ℝ)^d)^2) = (2:ℝ)^(8*d) := by
      rw [show (16:ℝ) = 2^4 by norm_num, ← pow_mul, ← pow_mul]
      congr 1; omega
    _ = (2:ℝ)^(8*(d:ℝ)) := by norm_cast
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
