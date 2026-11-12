-- Prove2me | solution 1 for DerivationHitting.Commutative.trivial_constants
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T22:20:55.206768+00:00
-- url     : https://prove2.me/submissions/9684d32f-65bb-4efe-be66-4d89a2c4c6df

import Definitions.Def_DerivationHitting_Commutative_DifferentialData

section
open scoped RatFunc
open DerivationHitting.Commutative

namespace DerivationHitting.Dev.XFree
noncomputable section

variable {F : Type*} [Field F]

/-- quotient rule for any representation -/
theorem rd_div (p q : Polynomial F) (hq : q ≠ 0) :
    rationalDerivative (algebraMap (Polynomial F) (RatFunc F) p /
      algebraMap (Polynomial F) (RatFunc F) q) =
    algebraMap (Polynomial F) (RatFunc F) (p.derivative * q - p * q.derivative) /
      (algebraMap (Polynomial F) (RatFunc F) q) ^ 2 := by
  set a := algebraMap (Polynomial F) (RatFunc F) p /
      algebraMap (Polynomial F) (RatFunc F) q with ha
  have hqne : algebraMap (Polynomial F) (RatFunc F) q ≠ 0 := RatFunc.algebraMap_ne_zero hq
  have hd : algebraMap (Polynomial F) (RatFunc F) a.denom ≠ 0 :=
    RatFunc.algebraMap_ne_zero (RatFunc.denom_ne_zero a)
  have h1 : a.num * q = p * a.denom := by
    apply RatFunc.algebraMap_injective F
    have := RatFunc.num_div_denom a
    rw [map_mul, map_mul]
    rw [div_eq_div_iff hd hqne] at this
    exact this
  have h2 := congrArg Polynomial.derivative h1
  simp only [Polynomial.derivative_mul] at h2
  unfold rationalDerivative
  rw [div_eq_div_iff (pow_ne_zero _ hd) (pow_ne_zero _ hqne), ← map_pow, ← map_pow, ← map_mul,
    ← map_mul]
  congr 1
  linear_combination (a.denom * q) * h2 + (-(a.denom.derivative * q) - q.derivative * a.denom) * h1

theorem rd_zero : rationalDerivative (0 : RatFunc F) = 0 := by
  have := rd_div (F := F) 0 1 one_ne_zero
  simpa using this

theorem rd_repr (a : RatFunc F) :
    ∃ p q : Polynomial F, q ≠ 0 ∧ a = algebraMap (Polynomial F) (RatFunc F) p /
      algebraMap (Polynomial F) (RatFunc F) q :=
  ⟨a.num, a.denom, RatFunc.denom_ne_zero a, (RatFunc.num_div_denom a).symm⟩

theorem rd_mul_alg (c : F) (a : RatFunc F) :
    rationalDerivative (algebraMap F (RatFunc F) c * a) =
      algebraMap F (RatFunc F) c * rationalDerivative a := by
  obtain ⟨p, q, h1, rfl⟩ := rd_repr a
  have e1 : algebraMap (Polynomial F) (RatFunc F) q ≠ 0 := RatFunc.algebraMap_ne_zero h1
  have hc : algebraMap (Polynomial F) (RatFunc F) (Polynomial.C c) = algebraMap F (RatFunc F) c :=
    rfl
  have : algebraMap F (RatFunc F) c * (algebraMap (Polynomial F) (RatFunc F) p /
      algebraMap (Polynomial F) (RatFunc F) q) =
      algebraMap (Polynomial F) (RatFunc F) (Polynomial.C c * p) /
        algebraMap (Polynomial F) (RatFunc F) q := by
    rw [map_mul, hc, mul_div_assoc]
  rw [this, rd_div _ _ h1, rd_div _ _ h1]
  simp only [map_mul, map_sub, Polynomial.derivative_mul, Polynomial.derivative_C,
    zero_mul, zero_add]
  rw [hc]
  ring

variable {n : ℕ}

theorem coeff_T (h : MvPolynomial (Fin n) (RatFunc F)) (m : Fin n →₀ ℕ) :
    MvPolynomial.coeff m (timeDerivative h) = rationalDerivative (MvPolynomial.coeff m h) := by
  classical
  unfold timeDerivative
  rw [MvPolynomial.coeff_sum]
  simp only [MvPolynomial.coeff_monomial]
  by_cases hm : m ∈ h.support
  · rw [Finset.sum_eq_single m]
    · simp
    · intro m' _ hne; simp [hne]
    · intro hn; exact absurd hm hn
  · rw [Finset.sum_eq_zero]
    · have : MvPolynomial.coeff m h = 0 := by simpa using hm
      rw [this, rd_zero]
    · intro m' hm'
      have : m' ≠ m := fun e => hm (e ▸ hm')
      simp [this]

section Det

variable {A : Type*} [CommRing A] {K : Type*} [CommRing K] [Algebra K A]

end Det

end
end DerivationHitting.Dev.XFree

namespace DerivationHitting.Commutative
open DerivationHitting.Dev.XFree

end DerivationHitting.Commutative
end

section
open scoped RatFunc
open DerivationHitting.Commutative DerivationHitting.Dev.XFree

namespace DerivationHitting.Dev.TrivConst
noncomputable section

variable {F : Type*} [Field F]

/-- L1: zero derivative means constant. -/
theorem rd_eq_zero [CharZero F] (a : RatFunc F) (h : rationalDerivative a = 0) :
    ∃ c : F, a = algebraMap F (RatFunc F) c := by
  have hq : a.denom ≠ 0 := RatFunc.denom_ne_zero a
  have hqe : algebraMap (Polynomial F) (RatFunc F) a.denom ≠ 0 := RatFunc.algebraMap_ne_zero hq
  have h1 := rd_div a.num a.denom hq
  rw [RatFunc.num_div_denom, h] at h1
  have h2 : algebraMap (Polynomial F) (RatFunc F)
      (a.num.derivative * a.denom - a.num * a.denom.derivative) = 0 := by
    have := h1.symm
    rw [div_eq_zero_iff] at this
    exact this.resolve_right (pow_ne_zero _ hqe)
  have h3 : a.num.derivative * a.denom = a.num * a.denom.derivative := by
    have := (map_eq_zero_iff _ (RatFunc.algebraMap_injective F)).1 h2
    exact sub_eq_zero.1 this
  have hcop : IsCoprime a.denom a.num := (RatFunc.isCoprime_num_denom a).symm
  have h4 : a.denom ∣ a.denom.derivative := by
    apply hcop.dvd_of_dvd_mul_left
    rw [← h3]; exact dvd_mul_left _ _
  have h5 : a.denom.derivative = 0 := by
    by_contra hne
    have hle := Polynomial.natDegree_le_of_dvd h4 hne
    by_cases hd : a.denom.natDegree = 0
    · exact hne (Polynomial.derivative_of_natDegree_zero hd)
    · have := Polynomial.natDegree_derivative_lt hd
      omega
  have h6 : a.denom = Polynomial.C (a.denom.coeff 0) := Polynomial.eq_C_of_derivative_eq_zero h5
  rw [h5, mul_zero] at h3
  have h7 : a.num.derivative = 0 := (mul_eq_zero.1 h3).resolve_right hq
  have h8 : a.num = Polynomial.C (a.num.coeff 0) := Polynomial.eq_C_of_derivative_eq_zero h7
  have hc : a.denom.coeff 0 ≠ 0 := by
    intro e; apply hq; rw [h6, e]; simp
  refine ⟨a.num.coeff 0 / a.denom.coeff 0, ?_⟩
  have e : a = algebraMap _ _ a.num / algebraMap _ _ a.denom := (RatFunc.num_div_denom a).symm
  rw [h8, h6] at e
  refine e.trans ?_
  rw [map_div₀]
  rfl

open Polynomial in
/-- L2, polynomial form of the residue argument. -/
theorem residue_poly [CharZero F] {n : ℕ} (r : Fin n → F) (hr : Function.Injective r)
    (l : Fin n → F) (p q : Polynomial F) (hq : q ≠ 0) (hcop : IsCoprime p q) (j : Fin n)
    (hlj : l j ≠ 0)
    (star : q ^ 2 * ∑ i, C (l i) * ∏ x ∈ Finset.univ.erase i, (X - C (r x)) =
      (derivative p * q - p * derivative q) * ∏ x, (X - C (r x))) : False := by
  classical
  set Qj : Polynomial F := ∏ x ∈ Finset.univ.erase j, (X - C (r x)) with hQj
  set S : Polynomial F := ∑ i, C (l i) * ∏ x ∈ Finset.univ.erase i, (X - C (r x)) with hS
  have hQ : ∏ x, (X - C (r x)) = (X - C (r j)) * Qj :=
    (Finset.mul_prod_erase Finset.univ (fun x => X - C (r x)) (Finset.mem_univ j)).symm
  rw [hQ] at star
  have hQj0 : Qj.eval (r j) ≠ 0 := by
    rw [hQj, Polynomial.eval_prod]
    refine Finset.prod_ne_zero_iff.2 fun x hx => ?_
    have : x ≠ j := Finset.ne_of_mem_erase hx
    simp only [eval_sub, eval_X, eval_C]
    exact sub_ne_zero.2 (fun e => this (hr e).symm)
  have hS0 : S.eval (r j) = l j * Qj.eval (r j) := by
    rw [hS, Polynomial.eval_finset_sum, Finset.sum_eq_single j]
    · simp [hQj]
    · intro i _ hij
      have : (∏ x ∈ Finset.univ.erase i, (X - C (r x))).eval (r j) = 0 := by
        rw [Polynomial.eval_prod]
        exact Finset.prod_eq_zero (Finset.mem_erase.2 ⟨Ne.symm hij, Finset.mem_univ j⟩) (by simp)
      simp [this]
    · intro h; exact absurd (Finset.mem_univ j) h
  by_cases hroot : q.IsRoot (r j)
  · -- pole case
    obtain ⟨q0, hq0, hndvd⟩ := Polynomial.exists_eq_pow_rootMultiplicity_mul_and_not_dvd q hq (r j)
    have hv : 0 < q.rootMultiplicity (r j) := (Polynomial.rootMultiplicity_pos hq).2 hroot
    obtain ⟨w, hw⟩ : ∃ w, q.rootMultiplicity (r j) = w + 1 := ⟨_, (Nat.succ_pred_eq_of_pos hv).symm⟩
    rw [hw] at hq0
    have hq00 : q0.eval (r j) ≠ 0 := fun e => hndvd ((Polynomial.dvd_iff_isRoot).2 e)
    have hp0 : p.eval (r j) ≠ 0 := by
      intro e
      obtain ⟨a, b, hab⟩ := hcop
      have := congrArg (Polynomial.eval (r j)) hab
      simp [e, hroot.eq_zero] at this
    have hdq : derivative q = ((w + 1 : ℕ) : Polynomial F) * (X - C (r j)) ^ w * q0 +
        (X - C (r j)) ^ (w + 1) * derivative q0 := by
      conv_lhs => rw [hq0]
      simp only [derivative_mul, derivative_pow, derivative_sub, derivative_X, derivative_C]
      simp
    set B : Polynomial F := derivative p * (X - C (r j)) * q0 -
      p * (((w + 1 : ℕ) : Polynomial F) * q0 + (X - C (r j)) * derivative q0) with hB
    have hne : ((X : Polynomial F) - C (r j)) ^ (w + 1) ≠ 0 := pow_ne_zero _ (X_sub_C_ne_zero _)
    have key : (X - C (r j)) ^ (w + 1) * ((X - C (r j)) ^ (w + 1) * (q0 ^ 2 * S)) =
        (X - C (r j)) ^ (w + 1) * (B * Qj) := by
      rw [hdq, hq0] at star
      rw [hB]
      linear_combination star
    have key2 := mul_left_cancel₀ hne key
    have := congrArg (Polynomial.eval (r j)) key2
    simp only [eval_mul, eval_pow, eval_sub, eval_X, eval_C, sub_self] at this
    rw [zero_pow (Nat.succ_ne_zero _), zero_mul] at this
    simp only [hB, eval_mul, eval_sub, eval_X, eval_C, sub_self, mul_zero, zero_mul, eval_add,
      eval_natCast, zero_sub] at this
    have hc : ((w + 1 : ℕ) : F) ≠ 0 := Nat.cast_ne_zero.2 (Nat.succ_ne_zero _)
    rw [add_zero] at this
    exact mul_ne_zero (neg_ne_zero.2 (mul_ne_zero hp0 (mul_ne_zero hc hq00))) hQj0 this.symm
  · have := congrArg (Polynomial.eval (r j)) star
    simp only [eval_mul, eval_pow, eval_sub, eval_X, eval_C, sub_self, mul_zero, zero_mul] at this
    rw [hS0] at this
    have hq1 : q.eval (r j) ≠ 0 := hroot
    exact mul_ne_zero (pow_ne_zero 2 hq1) (mul_ne_zero hlj hQj0) this

def rpt {n : ℕ} (i : Fin n) : F := -(1 / ((i.val + 1 : ℕ) : F))

theorem rpt_inj [CharZero F] {n : ℕ} : Function.Injective (rpt (F := F) (n := n)) := by
  intro i j h
  unfold rpt at h
  have h1 : (1 / ((i.val + 1 : ℕ) : F)) = 1 / ((j.val + 1 : ℕ) : F) := neg_injective h
  have hi : ((i.val + 1 : ℕ) : F) ≠ 0 := Nat.cast_ne_zero.2 (Nat.succ_ne_zero _)
  have hj : ((j.val + 1 : ℕ) : F) ≠ 0 := Nat.cast_ne_zero.2 (Nat.succ_ne_zero _)
  have h2 : ((i.val + 1 : ℕ) : F) = ((j.val + 1 : ℕ) : F) := by
    have := congrArg (fun x => 1 / x) h1
    simpa using this
  have := Nat.cast_injective h2
  exact Fin.ext (by omega)

theorem kernel_eq [CharZero F] {n : ℕ} (i : Fin n) :
    logarithmKernel (F := F) i =
      1 / (RatFunc.X - algebraMap F (RatFunc F) (rpt i)) := by
  unfold logarithmKernel rpt
  have hi : ((i.val + 1 : ℕ) : F) ≠ 0 := Nat.cast_ne_zero.2 (Nat.succ_ne_zero _)
  have hi' : algebraMap F (RatFunc F) ((i.val + 1 : ℕ) : F) ≠ 0 :=
    (map_ne_zero (algebraMap F (RatFunc F))).2 hi
  have e : (1 : RatFunc F) + algebraMap F (RatFunc F) ((i.val + 1 : ℕ) : F) * RatFunc.X =
      algebraMap F (RatFunc F) ((i.val + 1 : ℕ) : F) *
        (RatFunc.X - algebraMap F (RatFunc F) (-(1 / ((i.val + 1 : ℕ) : F)))) := by
    rw [map_neg, map_div₀, map_one]
    field_simp
    ring
  rw [e, div_mul_eq_div_div, div_self hi', one_div]

open Polynomial in
theorem residue [CharZero F] {n : ℕ} (l : Fin n → F) (a : RatFunc F)
    (H : ∑ i, algebraMap F (RatFunc F) (l i) * logarithmKernel i = rationalDerivative a) :
    ∀ j, l j = 0 := by
  classical
  intro j
  by_contra hlj
  have hq : a.denom ≠ 0 := RatFunc.denom_ne_zero a
  have hqe : algebraMap (Polynomial F) (RatFunc F) a.denom ≠ 0 := RatFunc.algebraMap_ne_zero hq
  refine residue_poly rpt rpt_inj l a.num a.denom hq (RatFunc.isCoprime_num_denom a) j hlj ?_
  apply RatFunc.algebraMap_injective F
  have hrd := rd_div a.num a.denom hq
  rw [RatFunc.num_div_denom] at hrd
  have hy : ∀ i : Fin n, algebraMap (Polynomial F) (RatFunc F) (X - C (rpt i)) =
      RatFunc.X - algebraMap F (RatFunc F) (rpt i) := by
    intro i
    rw [map_sub, RatFunc.algebraMap_X]
    rfl
  have hy0 : ∀ i : Fin n, RatFunc.X - algebraMap F (RatFunc F) (rpt i) ≠ 0 := by
    intro i; rw [← hy]; exact RatFunc.algebraMap_ne_zero (X_sub_C_ne_zero _)
  have key : ∀ i : Fin n, algebraMap (Polynomial F) (RatFunc F)
      (∏ x ∈ Finset.univ.erase i, (X - C (rpt x))) =
      algebraMap (Polynomial F) (RatFunc F) (∏ x, (X - C (rpt (n := n) x : F))) * logarithmKernel i := by
    intro i
    rw [kernel_eq, ← Finset.mul_prod_erase Finset.univ (fun x => X - C (rpt (n := n) x : F))
      (Finset.mem_univ i), map_mul, hy]
    field_simp [hy0 i]
    exact (mul_div_cancel_right₀ _ (hy0 i)).symm
  have hsum : algebraMap (Polynomial F) (RatFunc F)
      (∑ i, C (l i) * ∏ x ∈ Finset.univ.erase i, (X - C (rpt (n := n) x : F))) =
      algebraMap (Polynomial F) (RatFunc F) (∏ x, (X - C (rpt (n := n) x : F))) *
        rationalDerivative a := by
    rw [← H, map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, key]
    have : algebraMap (Polynomial F) (RatFunc F) (C (l i)) = algebraMap F (RatFunc F) (l i) := rfl
    rw [this]; ring
  rw [map_mul, map_mul, map_pow, hsum, hrd]
  field_simp

theorem rd_neg (x : RatFunc F) : rationalDerivative (-x) = -rationalDerivative x := by
  have := rd_mul_alg (-1 : F) x
  simpa using this

variable {n : ℕ}

theorem coeff_D (b : Fin n → RatFunc F) (h : MvPolynomial (Fin n) (RatFunc F))
    (m : Fin n →₀ ℕ) :
    MvPolynomial.coeff m (linearDerivation b h) = rationalDerivative (MvPolynomial.coeff m h) +
      ∑ i, b i * (MvPolynomial.coeff (m + Finsupp.single i 1) h * ((m i : RatFunc F) + 1)) := by
  unfold linearDerivation
  rw [MvPolynomial.coeff_add, coeff_T, MvPolynomial.coeff_sum]
  simp only [MvPolynomial.coeff_C_mul, MvPolynomial.coeff_pderiv]

def deg (m : Fin n →₀ ℕ) : ℕ := ∑ i, m i

theorem deg_add_single (m : Fin n →₀ ℕ) (i : Fin n) : deg (m + Finsupp.single i 1) = deg m + 1 := by
  classical
  simp [deg, Finset.sum_add_distrib, Finsupp.single_apply]

theorem deg_pos (m : Fin n →₀ ℕ) (i : Fin n) (hi : m i ≠ 0) : 1 ≤ deg m := by
  have : m i ≤ deg m := Finset.single_le_sum (f := fun i => m i) (fun _ _ => Nat.zero_le _)
    (Finset.mem_univ i)
  omega

end
end DerivationHitting.Dev.TrivConst

namespace DerivationHitting.Commutative
open DerivationHitting.Dev.TrivConst DerivationHitting.Dev.XFree

theorem chk_trivial_constants {F : Type*} [Field F] [CharZero F] (n : ℕ) :
    hasTrivialConstants (F := F) (n := n) logarithmKernel := by
  classical
  intro h
  constructor
  swap
  · rintro ⟨c, rfl⟩
    ext m
    rw [coeff_D, MvPolynomial.coeff_C]
    by_cases hm : 0 = m
    · subst hm
      simp only [if_true, MvPolynomial.coeff_zero]
      have h0 : rationalDerivative (algebraMap F (RatFunc F) c) = 0 := by
        have := rd_mul_alg c 1
        have h1 : rationalDerivative (1 : RatFunc F) = 0 := by
          have := rd_div (F := F) 1 1 one_ne_zero
          simpa using this
        simpa [h1] using this
      rw [h0, zero_add]
      refine Finset.sum_eq_zero fun i _ => ?_
      have : (0 : Fin n →₀ ℕ) + Finsupp.single i 1 ≠ 0 := by
        intro e; have := congrArg (fun f => f i) e; simp at this
      rw [MvPolynomial.coeff_C, if_neg (Ne.symm this)]; simp
    · rw [if_neg hm, rd_zero, zero_add]
      refine Finset.sum_eq_zero fun i _ => ?_
      have : ¬ (0 = m + Finsupp.single i 1) := by
        intro e
        have := congrArg (fun f => f i) e
        simp at this
      rw [MvPolynomial.coeff_C, if_neg this]; simp
  · intro hD
    have hE : ∀ m, rationalDerivative (MvPolynomial.coeff m h) +
        ∑ i, logarithmKernel i * (MvPolynomial.coeff (m + Finsupp.single i 1) h *
          ((m i : RatFunc F) + 1)) = 0 := by
      intro m
      have := congrArg (MvPolynomial.coeff m) hD
      rwa [coeff_D, MvPolynomial.coeff_zero] at this
    have hne : ∀ (m : Fin n →₀ ℕ) i, ¬ (0 = m + Finsupp.single i 1) := by
      intro m i e
      have := congrArg (fun f => f i) e
      simp at this
    by_cases hc : ∀ m, m ≠ 0 → MvPolynomial.coeff m h = 0
    · have h0 := hE 0
      have hz : ∑ i, logarithmKernel (F := F) i * (MvPolynomial.coeff (0 + Finsupp.single i 1) h *
          (((0 : Fin n →₀ ℕ) i : RatFunc F) + 1)) = 0 := by
        refine Finset.sum_eq_zero fun i _ => ?_
        rw [hc _ (fun e => hne 0 i e.symm)]; simp
      rw [hz, add_zero] at h0
      obtain ⟨c, hc0⟩ := rd_eq_zero _ h0
      refine ⟨c, ?_⟩
      ext m
      rw [MvPolynomial.coeff_C]
      by_cases hm : 0 = m
      · subst hm; simpa using hc0
      · rw [if_neg hm, hc _ (Ne.symm hm)]
    · push Not at hc
      obtain ⟨m1, hm1, hne1⟩ := hc
      have hsupp : m1 ∈ h.support := MvPolynomial.mem_support_iff.2 hne1
      obtain ⟨m, hm, hmax⟩ := Finset.exists_max_image h.support deg ⟨m1, hsupp⟩
      obtain ⟨i1, hi1⟩ : ∃ i, m1 i ≠ 0 := by
        by_contra hcon
        push Not at hcon
        exact hm1 (Finsupp.ext hcon)
      have hd1 : 1 ≤ deg m := le_trans (deg_pos m1 i1 hi1) (hmax m1 hsupp)
      obtain ⟨i, hi⟩ : ∃ i, m i ≠ 0 := by
        by_contra hcon
        push Not at hcon
        have : m = 0 := Finsupp.ext hcon
        subst this
        simp [deg] at hd1
      have hle : Finsupp.single i 1 ≤ m := by
        rw [Finsupp.single_le_iff]; omega
      obtain ⟨m', hm'⟩ : ∃ m' : Fin n →₀ ℕ, m = m' + Finsupp.single i 1 :=
        ⟨m - Finsupp.single i 1, (tsub_add_cancel_of_le hle).symm⟩
      -- top coefficients are constants
      have top : ∀ l : Fin n, ∃ c : F,
          MvPolynomial.coeff (m' + Finsupp.single l 1) h = algebraMap F (RatFunc F) c := by
        intro l
        apply rd_eq_zero
        have h2 := hE (m' + Finsupp.single l 1)
        have hz : ∑ k, logarithmKernel (F := F) k *
            (MvPolynomial.coeff (m' + Finsupp.single l 1 + Finsupp.single k 1) h *
              (((((m' + Finsupp.single l 1 : Fin n →₀ ℕ)) k : ℕ) : RatFunc F) + 1)) = 0 := by
          refine Finset.sum_eq_zero fun k _ => ?_
          have : MvPolynomial.coeff (m' + Finsupp.single l 1 + Finsupp.single k 1) h = 0 := by
            by_contra hcc
            have := hmax _ (MvPolynomial.mem_support_iff.2 hcc)
            rw [deg_add_single, deg_add_single, hm', deg_add_single] at this
            rw [hm', deg_add_single] at hmax
            omega
          rw [this]; simp
        rwa [hz, add_zero] at h2
      choose c hc using top
      have h3 := hE m'
      have hsum : ∑ l, algebraMap F (RatFunc F) (c l * (((m' l + 1 : ℕ)) : F)) *
          logarithmKernel (F := F) l = rationalDerivative (-(MvPolynomial.coeff m' h)) := by
        rw [rd_neg, eq_neg_iff_add_eq_zero, add_comm, ← h3]
        congr 1
        refine Finset.sum_congr rfl fun l _ => ?_
        rw [hc l, map_mul]
        push_cast
        ring
      have hres := residue _ _ hsum i
      have hci : c i = 0 := by
        have : ((m' i + 1 : ℕ) : F) ≠ 0 := Nat.cast_ne_zero.2 (Nat.succ_ne_zero _)
        exact (mul_eq_zero.1 hres).resolve_right this
      exfalso
      exact (MvPolynomial.mem_support_iff.1 hm) (by rw [hm', hc i, hci, map_zero])

end DerivationHitting.Commutative
end

theorem solution : type_of% @DerivationHitting.Commutative.chk_trivial_constants := @DerivationHitting.Commutative.chk_trivial_constants
