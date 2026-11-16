-- Prove2me | solution 1 for FourierDimTesting102.Quantum.Supplement.shift_agreement_prob
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-15T09:57:48.793513+00:00
-- url     : https://prove2.me/submissions/959a010f-28ef-4ec7-879e-eceb06dc6118

import Mathlib
import Definitions.Def_FourierDimTesting102_Quantum_Supplement_Model

open QAlgorithms FourierDimTesting102.Quantum FourierDimTesting102.Quantum.Supplement

lemma sap_coeff_eq {n : ℕ} (f : BoolFn n) (s : V n) :
    coeff f s = ((2 : ℝ) ^ n)⁻¹ * ∑ y : V n, toSign f y * chi s y := by
  simp [coeff, boolFourier, chi]

lemma sap_sum_chi {n : ℕ} (t : V n) :
    ∑ s : V n, chi t s = if t = 0 then (2 : ℝ) ^ n else 0 := by
  split_ifs with ht
  · subst ht; simp [chi, Fintype.card_fun, ZMod.card]
  · exact sum_chi_eq_zero ht

lemma sap_add_eq_zero {n : ℕ} (y x : V n) : y + x = 0 ↔ y = x := by
  constructor
  · intro h; funext i
    have := congrFun h i
    simp at this
    have h2 : ∀ a b : ZMod 2, a + b = 0 → a = b := by decide
    exact h2 _ _ this
  · intro h; subst h; funext i
    have h2 : ∀ a : ZMod 2, a + a = 0 := by decide
    exact h2 (y i)

lemma sap_inversion {n : ℕ} (f : BoolFn n) (x : V n) :
    toSign f x = ∑ s : V n, coeff f s * chi s x := by
  simp_rw [sap_coeff_eq, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  have : ∀ y : V n, ∑ s : V n, ((2 : ℝ) ^ n)⁻¹ * (toSign f y * chi s y) * chi s x
      = ((2 : ℝ) ^ n)⁻¹ * toSign f y * (if y + x = 0 then (2 : ℝ) ^ n else 0) := by
    intro y
    rw [← sap_sum_chi, Finset.mul_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [chi_comm (y + x) s, chi_add_right]; ring
  simp_rw [this, sap_add_eq_zero]
  simp only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  field_simp

lemma sap_corr {n : ℕ} (f : BoolFn n) (x y : V n) :
    ∑ z : V n, toSign f (x + z) * toSign f (y + z) =
      (2 : ℝ) ^ n * ∑ s : V n, coeff f s ^ 2 * chi s (x + y) := by
  have hinner : ∀ s : V n, ∑ z : V n, toSign f (x + z) * chi s (y + z) =
      chi s (x + y) * ((2 : ℝ) ^ n * coeff f s) := by
    intro s
    rw [sap_coeff_eq, ← mul_assoc ((2 : ℝ) ^ n), mul_inv_cancel₀ (by positivity : (2 : ℝ) ^ n ≠ 0),
      one_mul, Finset.mul_sum]
    rw [← Equiv.sum_comp (Equiv.addRight x)]
    refine Finset.sum_congr rfl fun w _ => ?_
    simp only [Equiv.coe_addRight]
    have e1 : x + (w + x) = w := by
      funext i; have h2 : ∀ a b : ZMod 2, a + (b + a) = b := by decide
      exact h2 (x i) (w i)
    have e2 : y + (w + x) = w + (x + y) := by
      funext i; have h2 : ∀ a b c : ZMod 2, c + (b + a) = b + (a + c) := by decide
      exact h2 (x i) (w i) (y i)
    rw [e1, e2, chi_add_right]; ring
  calc ∑ z : V n, toSign f (x + z) * toSign f (y + z)
      = ∑ z : V n, ∑ s : V n, coeff f s * (toSign f (x + z) * chi s (y + z)) := by
        refine Finset.sum_congr rfl fun z _ => ?_
        rw [sap_inversion f (y + z), Finset.mul_sum]
        refine Finset.sum_congr rfl fun s _ => ?_; ring
    _ = ∑ s : V n, coeff f s * ∑ z : V n, toSign f (x + z) * chi s (y + z) := by
        rw [Finset.sum_comm]; simp_rw [Finset.mul_sum]
    _ = ∑ s : V n, coeff f s * (chi s (x + y) * ((2 : ℝ) ^ n * coeff f s)) := by
        simp_rw [hinner]
    _ = _ := by rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun s _ => ?_; ring

lemma sap_toSign_sq {n : ℕ} (f : BoolFn n) (a : V n) : toSign f a * toSign f a = 1 := by
  unfold toSign signOf; split_ifs <;> norm_num

lemma sap_parseval {n : ℕ} (f : BoolFn n) : ∑ s : V n, coeff f s ^ 2 = 1 := by
  have h := sap_corr f 0 0
  simp only [zero_add, sap_toSign_sq, Finset.sum_const, Finset.card_univ] at h
  have hc : chi (n := n) = fun s x => chi s x := rfl
  have h0 : ∀ s : V n, chi s 0 = 1 := fun s => by simp [chi]
  simp only [h0, mul_one] at h
  have hcard : (Fintype.card (V n) : ℝ) = 2 ^ n := by simp [Fintype.card_fun, ZMod.card]
  simp only [nsmul_eq_mul, mul_one, hcard] at h
  have hp : (0 : ℝ) < 2 ^ n := by positivity
  nlinarith

lemma sap_ind (a b : Bool) :
    (if a = b then (1 : ℝ) else 0) = (1 + signOf a * signOf b) / 2 := by
  cases a <;> cases b <;> norm_num [signOf]

theorem solution {n : ℕ} (f : BoolFn n) (x y : V n) :
    unifProb (fun z : V n => f (x + z) = f (y + z)) =
      ∑ s ∈ Finset.univ.filter (fun s : V n => s ⬝ᵥ (x + y) = 0), coeff f s ^ 2 := by
  classical
  have hcard : (Fintype.card (V n) : ℝ) = 2 ^ n := by simp [Fintype.card_fun, ZMod.card]
  have hp : (0 : ℝ) < 2 ^ n := by positivity
  unfold unifProb
  rw [hcard]
  rw [Finset.card_filter]; push_cast
  have hcnt : ∀ z : V n, (if f (x + z) = f (y + z) then (1 : ℝ) else 0) =
      (1 + toSign f (x + z) * toSign f (y + z)) / 2 := by
    intro z
    by_cases h : f (x + z) = f (y + z)
    · rw [if_pos h]; unfold toSign; rw [h]; cases f (y + z) <;> norm_num [signOf]
    · rw [if_neg h]; unfold toSign
      cases hx : f (x + z) <;> cases hy : f (y + z) <;> simp_all [signOf]
  rw [Finset.sum_congr rfl (fun z _ => hcnt z), ← Finset.sum_div, Finset.sum_add_distrib, sap_corr]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, hcard]
  have hchi : ∀ s : V n, chi s (x + y) = if s ⬝ᵥ (x + y) = 0 then 1 else -1 := by
    intro s
    unfold chi
    have h2 : ∀ a : ZMod 2, (-1 : ℝ) ^ a.val = if a = 0 then 1 else -1 := by
      intro a
      rcases (show a = 0 ∨ a = 1 by revert a; decide) with h | h <;> subst h
      · simp
      · rw [if_neg (by decide)]; simp [ZMod.val_one]
    exact h2 _
  rw [Finset.sum_filter]
  have hpars := sap_parseval f
  have key : ∑ s : V n, coeff f s ^ 2 * chi s (x + y) =
      2 * ∑ s : V n, (if s ⬝ᵥ (x + y) = 0 then coeff f s ^ 2 else 0) - 1 := by
    rw [← hpars, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [hchi]; split_ifs <;> ring
  rw [key]
  field_simp
  ring
