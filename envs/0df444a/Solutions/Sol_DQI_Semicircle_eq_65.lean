-- Prove2me | solution 1 for DQI.Semicircle.eq_65
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-20T22:43:45.66196+00:00
-- url     : https://prove2.me/submissions/67cc00af-785d-4a9f-9e69-a7e4b907bc59

import Mathlib
import Definitions.Def_DQI_Semicircle_Setting

namespace Aux_DQI_Semicircle_eq_65

open DQI.Semicircle Polynomial

variable {p : ℕ} [Fact p.Prime] {m : ℕ}

lemma omega_eq (a : ZMod p) : omega a = (ZMod.stdAddChar (N := p) : AddChar (ZMod p) ℂ) a := by
  rw [ZMod.stdAddChar_apply, ZMod.toCircle_apply]
  rfl

lemma g_props (F : Fin m → Finset (ZMod p)) (r : ℕ) (hF : ∀ i, (F i).card = r) (hr : 1 ≤ r)
    (hrp : r < p) (i : Fin m) :
    ∑ a, g F i a = 0 ∧ ∑ a, (g F i a) ^ 2 = 1 := by
  have hp : (p : ℝ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hcard : Fintype.card (ZMod p) = p := ZMod.card p
  have hs0 : ∑ a, (fval F i a - fbar F i) = 0 := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, hcard, nsmul_eq_mul]
    unfold fbar
    rw [← mul_assoc, mul_one_div_cancel hp, one_mul, sub_self]
  obtain ⟨a, ha⟩ : (F i).Nonempty := Finset.card_pos.mp (by rw [hF]; omega)
  obtain ⟨b, hb⟩ : ∃ b, b ∉ F i := by
    by_contra hcon
    push_neg at hcon
    have h1 : F i = Finset.univ := Finset.eq_univ_of_forall hcon
    have h2 := congrArg Finset.card h1
    rw [hF, Finset.card_univ, hcard] at h2
    omega
  have hab : a ≠ b := fun h => hb (h ▸ ha)
  have hle : (fval F i a - fbar F i) ^ 2 + (fval F i b - fbar F i) ^ 2 ≤
      ∑ x, (fval F i x - fbar F i) ^ 2 := by
    have := Finset.sum_le_sum_of_subset_of_nonneg (s := {a, b}) (t := Finset.univ)
      (f := fun x => (fval F i x - fbar F i) ^ 2) (Finset.subset_univ _)
      (fun _ _ _ => sq_nonneg _)
    rw [Finset.sum_pair hab] at this
    exact this
  have hfa : fval F i a = 1 := if_pos ha
  have hfb : fval F i b = -1 := if_neg hb
  rw [hfa, hfb] at hle
  have hV : 0 < ∑ x, (fval F i x - fbar F i) ^ 2 := by nlinarith [sq_nonneg (fbar F i)]
  constructor
  · unfold g
    rw [← Finset.sum_div, hs0, zero_div]
  · unfold g
    simp only [div_pow]
    rw [← Finset.sum_div]
    unfold phi
    rw [Real.sq_sqrt hV.le, div_self hV.ne']

lemma gt_zero (F : Fin m → Finset (ZMod p)) (i : Fin m) (hg : ∑ a, g F i a = 0) :
    gt F i 0 = 0 := by
  unfold gt
  have h0 : ∀ x : ZMod p, omega (0 * x) = 1 := by
    intro x
    simp [omega]
  simp only [h0, one_mul]
  rw [← Complex.ofReal_sum, hg]
  simp


lemma omega_add (a b : ZMod p) : omega (a + b) = omega a * omega b := by
  rw [omega_eq, omega_eq, omega_eq, AddChar.map_add_eq_mul]

lemma omega_zero : omega (0 : ZMod p) = 1 := by
  rw [omega_eq, AddChar.map_zero_eq_one]

lemma omega_sum {ι : Type*} (s : Finset ι) (f : ι → ZMod p) :
    omega (∑ i ∈ s, f i) = ∏ i ∈ s, omega (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [omega_zero]
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.prod_insert hi, omega_add, ih]

lemma char_sum (b : ZMod p) : ∑ y : ZMod p, omega (y * b) = if b = 0 then (p : ℂ) else 0 := by
  simp only [omega_eq]
  rw [AddChar.sum_mulShift _ (ZMod.isPrimitive_stdAddChar p), ZMod.card]
  split_ifs <;> simp

lemma sqrt_sq_c : (1 / (Real.sqrt p : ℂ)) * (1 / (Real.sqrt p : ℂ)) = 1 / (p : ℂ) := by
  rw [div_mul_div_comm, one_mul, ← Complex.ofReal_mul,
    Real.mul_self_sqrt (Nat.cast_nonneg _), Complex.ofReal_natCast]

/-- Fourier inversion. -/
lemma inv (F : Fin m → Finset (ZMod p)) (i : Fin m) (a : ZMod p) :
    (g F i a : ℂ) = ∑ y : ZMod p, omega (-(y * a)) * ((1 / (Real.sqrt p : ℂ)) * gt F i y) := by
  have hp : (p : ℂ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  unfold gt
  have h1 : ∀ y : ZMod p, omega (-(y * a)) * ((1 / (Real.sqrt p : ℂ)) *
      ((1 / (Real.sqrt p : ℂ)) * ∑ x : ZMod p, omega (y * x) * (g F i x : ℂ))) =
      ∑ x : ZMod p, (1 / (p : ℂ)) * (g F i x : ℂ) * omega (y * (x - a)) := by
    intro y
    rw [← mul_assoc, ← mul_assoc, mul_assoc (omega _), sqrt_sq_c, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    rw [show y * (x - a) = y * x + -(y * a) by ring, omega_add]
    ring
  rw [Finset.sum_congr rfl (fun y _ => h1 y), Finset.sum_comm]
  simp_rw [← Finset.mul_sum, char_sum, sub_eq_zero]
  rw [Finset.sum_eq_single a]
  · rw [if_pos rfl]; field_simp
  · intro x _ hx; rw [if_neg hx, mul_zero]
  · intro h; exact absurd (Finset.mem_univ a) h

end Aux_DQI_Semicircle_eq_65

namespace Aux_DQI_Semicircle_eq_65

open DQI.Semicircle Polynomial

variable {p : ℕ} [Fact p.Prime] {m : ℕ}

/-- elementary symmetric functions of the `g_i(a_i)` in Fourier form. -/
lemma genE (F : Fin m → Finset (ZMod p)) (hgt0 : ∀ i, gt F i 0 = 0) (a : Fin m → ZMod p)
    (k : ℕ) :
    ∑ t ∈ Finset.univ.powersetCard k, ∏ i ∈ t, (g F i (a i) : ℂ) =
      ∑ y ∈ Finset.univ.filter (fun y : Fin m → ZMod p => wt y = k),
        omega (-(y ⬝ᵥ a)) * ((1 / (Real.sqrt p : ℂ)) ^ k * gtil F y) := by
  obtain ⟨Fy, hFy⟩ : ∃ Fy : Fin m → ZMod p → ℂ[X], Fy = fun i b =>
      C (omega (-(b * a i))) * (if b ≠ 0 then C ((1 / (Real.sqrt p : ℂ)) * gt F i b) * X else 1) := ⟨_, rfl⟩
  have hfac : ∀ i, ∑ b, Fy i b = 1 + C (g F i (a i) : ℂ) * X := by
    intro i
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : ZMod p))]
    have e1 : Fy i 0 = 1 := by simp [hFy, omega_zero]
    have e2 : ∀ b ∈ Finset.univ.erase (0 : ZMod p),
        Fy i b = C (omega (-(b * a i)) * ((1 / (Real.sqrt p : ℂ)) * gt F i b)) * X := by
      intro b hb
      simp only [hFy, if_pos (Finset.ne_of_mem_erase hb), map_mul]
      ring
    rw [e1, Finset.sum_congr rfl e2, ← Finset.sum_mul, ← map_sum,
      Finset.sum_erase_eq_sub (Finset.mem_univ _)]
    rw [hgt0 i, mul_zero, mul_zero, sub_zero, ← inv F i (a i)]
  have hP1 : ∏ i, (1 + C (g F i (a i) : ℂ) * X) =
      ∑ t ∈ (Finset.univ : Finset (Fin m)).powerset,
        C (∏ i ∈ t, (g F i (a i) : ℂ)) * X ^ t.card := by
    rw [Finset.prod_one_add]
    apply Finset.sum_congr rfl
    intro t _
    rw [Finset.prod_mul_distrib, Finset.prod_const, map_prod]
  have hP2 : ∀ y : Fin m → ZMod p, ∏ i, Fy i (y i) =
      C (omega (-(y ⬝ᵥ a)) * ((1 / (Real.sqrt p : ℂ)) ^ (wt y) * gtil F y)) * X ^ (wt y) := by
    intro y
    simp only [hFy]
    rw [Finset.prod_mul_distrib, Finset.prod_ite, Finset.prod_const_one, mul_one,
      Finset.prod_mul_distrib, Finset.prod_const, ← map_prod, ← map_prod]
    have hneg : -(y ⬝ᵥ a) = ∑ i, -(y i * a i) := by
      rw [dotProduct, ← Finset.sum_neg_distrib]
    rw [hneg, omega_sum]
    unfold gtil wt
    rw [Finset.prod_mul_distrib, Finset.prod_const]
    simp only [map_mul]
    ring
  have hpoly : ∑ t ∈ (Finset.univ : Finset (Fin m)).powerset,
        C (∏ i ∈ t, (g F i (a i) : ℂ)) * X ^ t.card =
      ∑ y : Fin m → ZMod p, C (omega (-(y ⬝ᵥ a)) * ((1 / (Real.sqrt p : ℂ)) ^ (wt y) * gtil F y)) * X ^ (wt y) := by
    rw [← hP1, Finset.prod_congr rfl (fun i _ => (hfac i).symm), Fintype.prod_sum Fy]
    exact Finset.sum_congr rfl (fun y _ => hP2 y)
  have hcoef := congrArg (fun P : ℂ[X] => P.coeff k) hpoly
  simp only [Polynomial.finset_sum_coeff, Polynomial.coeff_C_mul_X_pow, @eq_comm _ k] at hcoef
  rw [Finset.powersetCard_eq_filter, Finset.sum_filter, hcoef, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro y _
  by_cases hw : wt y = k
  · rw [if_pos hw, if_pos hw, hw]
  · rw [if_neg hw, if_neg hw]

/-- orthogonality on `(ZMod p)^n`. -/
lemma orth {n : ℕ} (u : Fin n → ZMod p) :
    ∑ x : Fin n → ZMod p, omega (u ⬝ᵥ x) = if u = 0 then ((p : ℂ) ^ n) else 0 := by
  have h1 : ∀ x : Fin n → ZMod p, omega (u ⬝ᵥ x) = ∏ j, omega (x j * u j) := by
    intro x
    rw [dotProduct, omega_sum]
    apply Finset.prod_congr rfl
    intro j _
    rw [mul_comm]
  rw [Finset.sum_congr rfl (fun x _ => h1 x)]
  rw [← Fintype.prod_sum (fun j b => omega (b * u j))]
  simp only [char_sum]
  rw [Finset.prod_ite_zero, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  by_cases hu : u = 0
  · rw [if_pos (fun j _ => by rw [hu]; rfl), if_pos hu]
  · rw [if_neg, if_neg hu]
    intro h
    apply hu
    funext j
    exact h j (Finset.mem_univ _)

lemma sqrt_pow' (x : ℝ) (hx : 0 ≤ x) (k : ℕ) : Real.sqrt (x ^ k) = Real.sqrt x ^ k := by
  rw [show x ^ k = (Real.sqrt x ^ k) ^ 2 by rw [← pow_mul, mul_comm, pow_mul, Real.sq_sqrt hx]]
  exact Real.sqrt_sq (pow_nonneg (Real.sqrt_nonneg _) _)

lemma coef (P C : ℝ) (hP : 0 < P) (hC : 0 ≤ C) (n k : ℕ) :
    (1 / Real.sqrt (P ^ n)) * (1 / Real.sqrt (P ^ ((n : ℤ) - (k : ℕ)) * C)) *
      (1 / Real.sqrt P) ^ k * P ^ n = 1 / Real.sqrt C := by
  have hS3 : (1 / Real.sqrt P) ^ k = 1 / Real.sqrt (P ^ k) := by
    rw [one_div_pow, sqrt_pow' P hP.le]
  have hkey : Real.sqrt (P ^ ((n : ℤ) - (k : ℕ)) * C) * Real.sqrt (P ^ k) =
      Real.sqrt (P ^ n) * Real.sqrt C := by
    rw [← Real.sqrt_mul (by positivity), ← Real.sqrt_mul (by positivity)]
    congr 1
    rw [mul_comm (P ^ ((n : ℤ) - (k : ℕ))) C, mul_assoc, ← zpow_natCast P k,
      ← zpow_add₀ hP.ne', sub_add_cancel, zpow_natCast, mul_comm]
  rw [hS3]
  obtain ⟨S1, hS1d⟩ : ∃ S, S = Real.sqrt (P ^ n) := ⟨_, rfl⟩
  obtain ⟨S2, hS2d⟩ : ∃ S, S = Real.sqrt (P ^ ((n : ℤ) - (k : ℕ)) * C) := ⟨_, rfl⟩
  obtain ⟨S3, hS3d⟩ : ∃ S, S = Real.sqrt (P ^ k) := ⟨_, rfl⟩
  obtain ⟨SC, hSCd⟩ : ∃ S, S = Real.sqrt C := ⟨_, rfl⟩
  rw [← hS1d, ← hS2d, ← hS3d, ← hSCd] at hkey
  rw [← hS1d, ← hS2d, ← hS3d, ← hSCd]
  have hS1 : S1 * S1 = P ^ n := by rw [hS1d]; exact Real.mul_self_sqrt (by positivity)
  have hS1pos : 0 < S1 := by rw [hS1d]; exact Real.sqrt_pos.mpr (by positivity)
  have hS3pos : 0 < S3 := by rw [hS3d]; exact Real.sqrt_pos.mpr (by positivity)
  rw [← hS1]
  by_cases hC0 : SC = 0
  · have hS2 : S2 = 0 := by
      rw [hC0, mul_zero] at hkey
      rcases mul_eq_zero.mp hkey with h | h
      · exact h
      · exact absurd h hS3pos.ne'
    rw [hS2, hC0]
    simp
  · have hSCpos : 0 < SC := lt_of_le_of_ne (by rw [hSCd]; exact Real.sqrt_nonneg _) (Ne.symm hC0)
    have hS2 : S2 = S1 * SC / S3 := by
      rw [← hkey]
      field_simp
    rw [hS2]
    field_simp <;> ring

end Aux_DQI_Semicircle_eq_65

open Aux_DQI_Semicircle_eq_65 in
open DQI.Semicircle in
theorem solution (p : ℕ) [Fact p.Prime] (m n : ℕ) (B : Matrix (Fin m) (Fin n) (ZMod p))
    (F : Fin m → Finset (ZMod p)) (r : ℕ) (hF : ∀ i, (F i).card = r) (hr : 1 ≤ r) (hrp : r < p)
    (hnm : n < m) (ℓ : ℕ) (w : Fin (ℓ + 1) → ℝ) (s : Fin n → ZMod p) :
    (1 / (Real.sqrt ((p : ℝ) ^ n) : ℂ)) * ∑ x : Fin n → ZMod p, omega (s ⬝ᵥ x) * (ampl B F ℓ w x : ℂ) =
      Ptilde B F ℓ w s := by
  have hgt0 : ∀ i, gt F i 0 = 0 := fun i => gt_zero F i (g_props F r hF hr hrp i).1
  have hE : ∀ (k : ℕ) (x : Fin n → ZMod p), ((esymmG B F k x : ℝ) : ℂ) =
      ∑ y ∈ Finset.univ.filter (fun y : Fin m → ZMod p => wt y = k),
        omega (-(y ⬝ᵥ B.mulVec x)) * ((1 / (Real.sqrt p : ℂ)) ^ k * gtil F y) := by
    intro k x
    unfold esymmG
    rw [Finset.esymm_map_val]
    push_cast
    exact genE F hgt0 (B.mulVec x) k
  have hF2 : ∀ y : Fin m → ZMod p, ∑ x : Fin n → ZMod p,
      omega (s ⬝ᵥ x) * omega (-(y ⬝ᵥ B.mulVec x)) =
        if B.transpose.mulVec y = s then (p : ℂ) ^ n else 0 := by
    intro y
    have h1 : ∀ x : Fin n → ZMod p, omega (s ⬝ᵥ x) * omega (-(y ⬝ᵥ B.mulVec x)) =
        omega ((s - B.transpose.mulVec y) ⬝ᵥ x) := by
      intro x
      rw [← omega_add, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, sub_dotProduct,
        sub_eq_add_neg]
    rw [Finset.sum_congr rfl (fun x _ => h1 x), orth]
    by_cases h : B.transpose.mulVec y = s
    · rw [if_pos (show s - B.transpose.mulVec y = 0 by rw [h, sub_self]), if_pos h]
    · rw [if_neg (show ¬ (s - B.transpose.mulVec y = 0) from
        fun h' => h (sub_eq_zero.mp h').symm), if_neg h]
  obtain ⟨A, hAd⟩ : ∃ A : Fin (ℓ + 1) → ℝ, A = fun k =>
      w k / Real.sqrt ((p : ℝ) ^ ((n : ℤ) - (k : ℕ)) * (m.choose k : ℝ)) := ⟨_, rfl⟩
  have hA : ∀ x, ((ampl B F ℓ w x : ℝ) : ℂ) =
      ∑ k : Fin (ℓ + 1), ((A k : ℝ) : ℂ) * ((esymmG B F k x : ℝ) : ℂ) := by
    intro x
    unfold ampl
    rw [hAd]
    push_cast
    apply Finset.sum_congr rfl
    intro k _
    ring
  have hstep : ∀ k : Fin (ℓ + 1),
      (1 / (Real.sqrt ((p : ℝ) ^ n) : ℂ)) *
        ∑ x : Fin n → ZMod p, omega (s ⬝ᵥ x) * (((A k : ℝ) : ℂ) * ((esymmG B F k x : ℝ) : ℂ)) =
      ((w k / Real.sqrt (m.choose (k : ℕ)) : ℝ) : ℂ) *
        ∑ y ∈ Finset.univ.filter (fun y : Fin m → ZMod p =>
          wt y = (k : ℕ) ∧ B.transpose.mulVec y = s), gtil F y := by
    intro k
    simp_rw [hE]
    have h2 : ∑ x : Fin n → ZMod p, omega (s ⬝ᵥ x) * (((A k : ℝ) : ℂ) *
        ∑ y ∈ Finset.univ.filter (fun y : Fin m → ZMod p => wt y = (k : ℕ)),
          omega (-(y ⬝ᵥ B.mulVec x)) * ((1 / (Real.sqrt p : ℂ)) ^ (k : ℕ) * gtil F y)) =
        ((A k : ℝ) : ℂ) * (1 / (Real.sqrt p : ℂ)) ^ (k : ℕ) *
          ∑ y ∈ Finset.univ.filter (fun y : Fin m → ZMod p => wt y = (k : ℕ)),
            gtil F y * ∑ x : Fin n → ZMod p, omega (s ⬝ᵥ x) * omega (-(y ⬝ᵥ B.mulVec x)) := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro y _
      apply Finset.sum_congr rfl
      intro x _
      ring
    rw [h2]
    simp_rw [hF2]
    have h3 : ∑ y ∈ Finset.univ.filter (fun y : Fin m → ZMod p => wt y = (k : ℕ)),
        gtil F y * (if B.transpose.mulVec y = s then (p : ℂ) ^ n else 0) =
        (p : ℂ) ^ n * ∑ y ∈ Finset.univ.filter (fun y : Fin m → ZMod p =>
          wt y = (k : ℕ) ∧ B.transpose.mulVec y = s), gtil F y := by
      rw [← Finset.filter_filter, Finset.sum_filter (s := Finset.univ.filter _), Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro y _
      split_ifs <;> ring
    rw [h3]
    have hc := coef (p : ℝ) (m.choose (k : ℕ) : ℝ)
      (by exact_mod_cast (Fact.out : p.Prime).pos) (Nat.cast_nonneg _) n k
    have hc' : (1 / (Real.sqrt ((p : ℝ) ^ n) : ℂ)) * (((A k : ℝ) : ℂ) *
        (1 / (Real.sqrt p : ℂ)) ^ (k : ℕ) * (p : ℂ) ^ n) =
        ((w k / Real.sqrt (m.choose (k : ℕ)) : ℝ) : ℂ) := by
      rw [hAd]
      have := congrArg (fun t : ℝ => ((w k * t : ℝ) : ℂ)) hc
      push_cast at this ⊢
      linear_combination this
    rw [← hc']
    ring
  unfold Ptilde
  have hL : (1 / (Real.sqrt ((p : ℝ) ^ n) : ℂ)) *
      ∑ x : Fin n → ZMod p, omega (s ⬝ᵥ x) * (ampl B F ℓ w x : ℂ) =
      ∑ k : Fin (ℓ + 1), (1 / (Real.sqrt ((p : ℝ) ^ n) : ℂ)) *
        ∑ x : Fin n → ZMod p, omega (s ⬝ᵥ x) * (((A k : ℝ) : ℂ) * ((esymmG B F k x : ℝ) : ℂ)) := by
    simp_rw [hA, Finset.mul_sum]
    rw [Finset.sum_comm]
  rw [hL]
  exact Finset.sum_congr rfl (fun k _ => hstep k)
