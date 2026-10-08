-- Prove2me | solution 1 for FuzzyGames.Values.owen_shapley
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T00:46:11.477975+00:00
-- url     : https://prove2.me/submissions/e387b466-5744-434b-811f-c9a237da3df2

import Mathlib
import Definitions.Def_FuzzyGames_Values_Basic
import Definitions.Def_Supermodularity_Cooperative_ShapleyValue

open Finset FuzzyGames.Values

theorem owen_regular (n : ℕ) (f : Finset (Fin n) → ℝ) (hf : f ∅ = 0) :
    owenExtension f ∈ Vn n := by
  constructor
  · unfold owenExtension
    apply ContDiff.sum
    intro A hA
    apply ContDiff.mul
    · apply ContDiff.mul contDiff_const
      apply contDiff_prod
      intro i hi
      exact contDiff_apply ℝ ℝ i
    · apply contDiff_prod
      intro i hi
      exact contDiff_const.sub (contDiff_apply ℝ ℝ i)
  · unfold owenExtension
    apply Finset.sum_eq_zero
    intro A hA
    by_cases h : A = ∅
    · subst A
      simp [hf]
    · have hprod : (∏ i ∈ A, (0 : Fin n → ℝ) i) = 0 := by
        obtain ⟨i, hi⟩ := Finset.nonempty_iff_ne_empty.mpr h
        exact Finset.prod_eq_zero hi rfl
      rw [hprod]
      ring


theorem beta_integral_nat (a b : ℕ) :
    (∫ t in (0 : ℝ)..1, t ^ a * (1 - t) ^ b) =
      (a.factorial : ℝ) * b.factorial / (a + b + 1).factorial := by
  have h := Complex.Gamma_mul_Gamma_eq_betaIntegral
    (s := (a : ℂ) + 1) (t := (b : ℂ) + 1) (by simp; positivity) (by simp; positivity)
  have he : (a : ℂ) + 1 + ((b : ℂ) + 1) = ((a + b + 1 : ℕ) : ℂ) + 1 := by
    push_cast
    ring
  rw [he, Complex.Gamma_nat_eq_factorial, Complex.Gamma_nat_eq_factorial,
    Complex.Gamma_nat_eq_factorial] at h
  have hn : ((a + b + 1).factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  have hb : Complex.betaIntegral ((a : ℂ) + 1) ((b : ℂ) + 1) =
      (a.factorial : ℂ) * b.factorial / (a + b + 1).factorial := by
    apply (eq_div_iff hn).mpr
    rw [mul_comm]
    exact h.symm
  have hi : Complex.betaIntegral ((a : ℂ) + 1) ((b : ℂ) + 1) =
      Complex.ofReal (∫ t in (0 : ℝ)..1, t ^ a * (1 - t) ^ b) := by
    unfold Complex.betaIntegral
    simp only [add_sub_cancel_right, Complex.cpow_natCast]
    rw [← intervalIntegral.integral_ofReal]
    congr 1
    funext t
    push_cast
    rfl
  apply Complex.ofReal_injective
  rw [← hi, hb]
  push_cast
  rfl


open Finset FuzzyGames.Values

namespace OwenProof

variable {n : ℕ}

noncomputable def leftProd (A : Finset (Fin n)) (τ : Fin n → ℝ) : ℝ := ∏ j ∈ A, τ j
noncomputable def rightProd (A : Finset (Fin n)) (τ : Fin n → ℝ) : ℝ := ∏ j ∈ A, (1 - τ j)

lemma left_smooth (A : Finset (Fin n)) : ContDiff ℝ 1 (leftProd A) := by
  exact contDiff_prod fun j hj => contDiff_apply ℝ ℝ j

lemma right_smooth (A : Finset (Fin n)) : ContDiff ℝ 1 (rightProd A) := by
  exact contDiff_prod fun j hj => contDiff_const.sub (contDiff_apply ℝ ℝ j)

lemma left_partial_zero (A : Finset (Fin n)) (i : Fin n) (hi : i ∉ A) (τ : Fin n → ℝ) :
    fderiv ℝ (leftProd A) τ (Pi.single i 1) = 0 := by
  have hd := HasFDerivAt.finset_prod (u := A) (fun j (_ : j ∈ A) => hasFDerivAt_apply j τ (𝕜 := ℝ))
  rw [show fderiv ℝ (leftProd A) τ = _ from hd.fderiv]
  simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.proj_apply, smul_eq_mul]
  apply Finset.sum_eq_zero
  intro j hj
  have hji : j ≠ i := by intro h; subst j; exact hi hj
  simp [Pi.single_eq_of_ne hji]

lemma right_partial_zero (A : Finset (Fin n)) (i : Fin n) (hi : i ∉ A) (τ : Fin n → ℝ) :
    fderiv ℝ (rightProd A) τ (Pi.single i 1) = 0 := by
  have hd := HasFDerivAt.finset_prod (u := A)
    (fun j (_ : j ∈ A) => (hasFDerivAt_const (1 : ℝ) τ).sub (hasFDerivAt_apply j τ (𝕜 := ℝ)))
  rw [show fderiv ℝ (rightProd A) τ = _ from hd.fderiv]
  simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.zero_apply,
    ContinuousLinearMap.proj_apply, smul_eq_mul]
  apply Finset.sum_eq_zero
  intro j hj
  have hji : j ≠ i := by intro h; subst j; exact hi hj
  simp [Pi.single_eq_of_ne hji]

lemma paired_extension (f : Finset (Fin n) → ℝ) (i : Fin n) :
    owenExtension f = fun τ => ∑ S ∈ (univ.erase i).powerset,
      (f S * (1 - τ i) + f (insert i S) * τ i) * leftProd S τ * rightProd (insert i S)ᶜ τ := by
  funext τ
  unfold owenExtension
  have hs := Finset.sum_powerset_insert (s := univ.erase i) (a := i) (by simp)
    (fun A => f A * (∏ j ∈ A, τ j) * ∏ j ∈ Aᶜ, (1 - τ j))
  rw [Finset.insert_erase (Finset.mem_univ i), Finset.powerset_univ] at hs
  rw [hs, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro S hS
  have hi : i ∉ S := by
    intro hi
    have hm := Finset.mem_powerset.mp hS hi
    simpa using hm
  have hc : Sᶜ = insert i (insert i S)ᶜ := by ext j; by_cases hj : j = i <;> simp [hj, hi]
  have hi' : i ∉ (insert i S)ᶜ := by simp
  simp only [leftProd, rightProd]
  rw [Finset.prod_insert hi, hc, Finset.prod_insert hi']
  ring

lemma paired_partial (f : Finset (Fin n) → ℝ) (i : Fin n) (S : Finset (Fin n))
    (hi : i ∉ S) (τ : Fin n → ℝ) :
    fderiv ℝ (fun τ => (f S * (1 - τ i) + f (insert i S) * τ i) *
      leftProd S τ * rightProd (insert i S)ᶜ τ) τ (Pi.single i 1) =
      (f (insert i S) - f S) * leftProd S τ * rightProd (insert i S)ᶜ τ := by
  let g : (Fin n → ℝ) → ℝ := fun τ => f S * (1 - τ i) + f (insert i S) * τ i
  have hg : ContDiff ℝ 1 g := by unfold g; fun_prop
  have hgd := ((hasFDerivAt_const (1 : ℝ) τ).sub (hasFDerivAt_apply i τ (𝕜 := ℝ))).const_mul (f S)
  have hgd' := (hasFDerivAt_apply i τ (𝕜 := ℝ)).const_mul (f (insert i S))
  have hge : fderiv ℝ g τ (Pi.single i 1) = f (insert i S) - f S := by
    rw [show fderiv ℝ g τ = _ from (hgd.add hgd').fderiv]
    simp
    ring
  have hL := (left_smooth S).differentiable (by norm_num) τ
  have hR := (right_smooth (insert i S)ᶜ).differentiable (by norm_num) τ
  have hG := hg.differentiable (by norm_num) τ
  change fderiv ℝ ((g * leftProd S) * rightProd (insert i S)ᶜ) τ _ = _
  rw [fderiv_mul (hG.mul hL) hR]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  rw [right_partial_zero _ i (by simp) τ, fderiv_mul hG hL]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  rw [left_partial_zero _ i hi τ, hge]
  ring

lemma diagonal_partial (f : Finset (Fin n) → ℝ) (i : Fin n) (t : ℝ) :
    fderiv ℝ (owenExtension f) (t • (1 : Fin n → ℝ)) (Pi.single i 1) =
      ∑ S ∈ (univ.erase i).powerset,
        (f (insert i S) - f S) * t ^ S.card * (1 - t) ^ (n - S.card - 1) := by
  rw [paired_extension f i]
  have hd : ∀ S ∈ (univ.erase i).powerset,
      DifferentiableAt ℝ (fun τ : Fin n → ℝ =>
        (f S * (1 - τ i) + f (insert i S) * τ i) * leftProd S τ * rightProd (insert i S)ᶜ τ)
        (t • (1 : Fin n → ℝ)) := by
    intro S hS
    have hg : ContDiff ℝ 1 (fun τ : Fin n → ℝ => f S * (1 - τ i) + f (insert i S) * τ i) := by fun_prop
    exact ((hg.mul (left_smooth S)).mul (right_smooth (insert i S)ᶜ)).differentiable (by norm_num) _
  rw [fderiv_fun_sum hd, ContinuousLinearMap.sum_apply]
  apply Finset.sum_congr rfl
  intro S hS
  have hi : i ∉ S := by
    intro hi
    have hm := Finset.mem_powerset.mp hS hi
    simpa using hm
  rw [paired_partial f i S hi]
  simp only [leftProd, rightProd, Pi.smul_apply, smul_eq_mul, Pi.one_apply, mul_one,
    Finset.prod_const, Finset.card_compl, Fintype.card_fin, Finset.card_insert_of_notMem hi]
  congr 2

lemma owen_value (f : Finset (Fin n) → ℝ) :
    diagValue (owenExtension f) = Supermodularity.Cooperative.ShapleyValue f := by
  funext i
  unfold diagValue Supermodularity.Cooperative.ShapleyValue
  simp_rw [diagonal_partial f i]
  rw [intervalIntegral.integral_finset_sum]
  · apply Finset.sum_congr rfl
    intro S hS
    rw [show (fun t : ℝ => (f (insert i S) - f S) * t ^ S.card * (1 - t) ^ (n - S.card - 1)) =
        (fun t : ℝ => (f (insert i S) - f S) * (t ^ S.card * (1 - t) ^ (n - S.card - 1))) by
      funext t; ring]
    rw [intervalIntegral.integral_const_mul, beta_integral_nat]
    have hi : i ∉ S := by
      intro hi
      have hm := Finset.mem_powerset.mp hS hi
      simpa using hm
    have hcard : S.card < n := by
      have hc := Finset.card_le_card (Finset.mem_powerset.mp hS)
      have hne : i ∈ (univ : Finset (Fin n)) := Finset.mem_univ i
      rw [Finset.card_erase_of_mem hne, Finset.card_univ, Fintype.card_fin] at hc
      have hin : i.val < n := i.isLt
      omega
    have he : S.card + (n - S.card - 1) + 1 = n := by omega
    rw [he]
    ring
  · intro S hS
    exact Continuous.intervalIntegrable (by fun_prop) _ _

end OwenProof

theorem solution (n : ℕ) (f : Finset (Fin n) → ℝ) (hf : f ∅ = 0) :
    owenExtension f ∈ Vn n ∧
      diagValue (owenExtension f) = Supermodularity.Cooperative.ShapleyValue f := by
  exact ⟨owen_regular n f hf, OwenProof.owen_value f⟩

#print axioms solution
