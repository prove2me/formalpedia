-- Prove2me | solution 1 for DerivationHitting.Commutative.wronskian_x_free
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T22:20:54.745976+00:00
-- url     : https://prove2.me/submissions/7e33596e-9308-4598-8ade-f605edbfb144

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

theorem rd_add (a b : RatFunc F) :
    rationalDerivative (a + b) = rationalDerivative a + rationalDerivative b := by
  obtain ⟨p1, q1, h1, rfl⟩ := rd_repr a
  obtain ⟨p2, q2, h2, rfl⟩ := rd_repr b
  have e1 : algebraMap (Polynomial F) (RatFunc F) q1 ≠ 0 := RatFunc.algebraMap_ne_zero h1
  have e2 : algebraMap (Polynomial F) (RatFunc F) q2 ≠ 0 := RatFunc.algebraMap_ne_zero h2
  have : algebraMap (Polynomial F) (RatFunc F) p1 / algebraMap (Polynomial F) (RatFunc F) q1 +
      algebraMap (Polynomial F) (RatFunc F) p2 / algebraMap (Polynomial F) (RatFunc F) q2 =
      algebraMap (Polynomial F) (RatFunc F) (p1 * q2 + p2 * q1) /
        algebraMap (Polynomial F) (RatFunc F) (q1 * q2) := by
    simp only [map_add, map_mul]
    field_simp
  rw [this, rd_div _ _ (mul_ne_zero h1 h2), rd_div _ _ h1, rd_div _ _ h2]
  simp only [map_add, map_mul, map_sub, Polynomial.derivative_mul, Polynomial.derivative_add, map_pow]
  field_simp
  ring

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

theorem rd_mul_natCast (a : RatFunc F) (k : ℕ) :
    rationalDerivative (a * (k : RatFunc F)) = rationalDerivative a * (k : RatFunc F) := by
  have : (k : RatFunc F) = algebraMap F (RatFunc F) (k : F) := (map_natCast _ k).symm
  rw [this, mul_comm, rd_mul_alg, mul_comm]

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

theorem T_add (h k : MvPolynomial (Fin n) (RatFunc F)) :
    timeDerivative (h + k) = timeDerivative h + timeDerivative k := by
  ext m; simp [coeff_T, rd_add]

theorem T_mul_alg (c : F) (h : MvPolynomial (Fin n) (RatFunc F)) :
    timeDerivative (MvPolynomial.C (algebraMap F (RatFunc F) c) * h) =
      MvPolynomial.C (algebraMap F (RatFunc F) c) * timeDerivative h := by
  ext m
  rw [coeff_T, MvPolynomial.coeff_C_mul, MvPolynomial.coeff_C_mul, coeff_T, rd_mul_alg]

theorem pderiv_comm (i k : Fin n) (h : MvPolynomial (Fin n) (RatFunc F)) :
    MvPolynomial.pderiv i (MvPolynomial.pderiv k h) =
      MvPolynomial.pderiv k (MvPolynomial.pderiv i h) := by
  classical
  ext m
  simp only [MvPolynomial.coeff_pderiv]
  rw [add_right_comm m]
  by_cases hik : i = k
  · subst hik; simp
  · simp [Finsupp.single_apply, hik, Ne.symm hik]
    ring

theorem T_pderiv (i : Fin n) (h : MvPolynomial (Fin n) (RatFunc F)) :
    timeDerivative (MvPolynomial.pderiv i h) = MvPolynomial.pderiv i (timeDerivative h) := by
  classical
  ext m
  rw [coeff_T, MvPolynomial.coeff_pderiv, MvPolynomial.coeff_pderiv, coeff_T]
  have : ((m i : RatFunc F) + 1) = ((m i + 1 : ℕ) : RatFunc F) := by push_cast; rfl
  rw [this, rd_mul_natCast]

theorem D_add (h k : MvPolynomial (Fin n) (RatFunc F)) (b : Fin n → RatFunc F) :
    linearDerivation b (h + k) = linearDerivation b h + linearDerivation b k := by
  unfold linearDerivation
  simp only [T_add, map_add, mul_add, Finset.sum_add_distrib]
  abel

theorem D_zero (b : Fin n → RatFunc F) : linearDerivation b 0 = 0 := by
  have := D_add (0 : MvPolynomial (Fin n) (RatFunc F)) 0 b
  simpa using this

theorem D_alg (b : Fin n → RatFunc F) (c : F) (h : MvPolynomial (Fin n) (RatFunc F)) :
    linearDerivation b (MvPolynomial.C (algebraMap F (RatFunc F) c) * h) =
      MvPolynomial.C (algebraMap F (RatFunc F) c) * linearDerivation b h := by
  unfold linearDerivation
  rw [T_mul_alg, mul_add, Finset.mul_sum]
  simp only [MvPolynomial.pderiv_C_mul]
  rw [add_right_inj]
  exact Finset.sum_congr rfl fun k _ => mul_left_comm _ _ _

theorem D_sum {ι : Type*} (b : Fin n → RatFunc F) (s : Finset ι)
    (f : ι → MvPolynomial (Fin n) (RatFunc F)) :
    linearDerivation b (∑ x ∈ s, f x) = ∑ x ∈ s, linearDerivation b (f x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using D_zero b
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, D_add, ih]

theorem D_comm (b : Fin n → RatFunc F) (i : Fin n) (h : MvPolynomial (Fin n) (RatFunc F)) :
    MvPolynomial.pderiv i (linearDerivation b h) = linearDerivation b (MvPolynomial.pderiv i h) := by
  unfold linearDerivation
  rw [map_add, T_pderiv, map_sum]
  rw [add_right_inj]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [MvPolynomial.pderiv_C_mul, pderiv_comm]

section Det

variable {A : Type*} [CommRing A] {K : Type*} [CommRing K] [Algebra K A]

theorem deriv_prod {ι : Type*} [DecidableEq ι] (δ : Derivation K A A) (s : Finset ι) (f : ι → A) :
    δ (∏ l ∈ s, f l) = ∑ j ∈ s, (∏ l ∈ s.erase j, f l) * δ (f j) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Derivation.leibniz, ih, Finset.sum_insert ha,
      Finset.erase_insert ha, smul_eq_mul, smul_eq_mul, Finset.mul_sum, add_comm]
    congr 1
    refine Finset.sum_congr rfl fun j hj => ?_
    have hne : a ≠ j := fun e => ha (e ▸ hj)
    rw [Finset.erase_insert_of_ne hne, Finset.prod_insert (fun h => ha (Finset.mem_of_mem_erase h))]
    ring

theorem deriv_det {q : ℕ} (δ : Derivation K A A) (M : Matrix (Fin q) (Fin q) A) :
    δ M.det = ∑ j, (M.updateCol j (fun r => δ (M r j))).det := by
  classical
  simp only [Matrix.det_apply, Units.smul_def, map_sum, map_zsmul]
  simp only [deriv_prod, Finset.smul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun σ _ => ?_
  congr 1
  rw [← Finset.prod_erase_mul Finset.univ _ (Finset.mem_univ j)]
  rw [Matrix.updateCol_apply, if_pos rfl]
  congr 1
  refine Finset.prod_congr rfl fun l hl => ?_
  rw [Matrix.updateCol_apply, if_neg (Finset.ne_of_mem_erase hl)]

end Det

theorem eq_C_of_pderiv_zero [CharZero F] (W : MvPolynomial (Fin n) (RatFunc F))
    (h : ∀ i, MvPolynomial.pderiv i W = 0) : ∃ a, W = MvPolynomial.C a := by
  classical
  haveI : CharZero (RatFunc F) := charZero_of_injective_algebraMap (algebraMap F (RatFunc F)).injective
  refine ⟨MvPolynomial.coeff 0 W, ?_⟩
  ext m
  rw [MvPolynomial.coeff_C]
  by_cases hm : 0 = m
  · subst hm; simp
  · rw [if_neg hm]
    obtain ⟨i, hi⟩ : ∃ i, m i ≠ 0 := by
      by_contra hcon
      push_neg at hcon
      exact hm (Finsupp.ext fun i => (hcon i).symm)
    have hle : Finsupp.single i 1 ≤ m := by
      rw [Finsupp.single_le_iff]; omega
    obtain ⟨m', hm'⟩ : ∃ m' : Fin n →₀ ℕ, m' = m - Finsupp.single i 1 := ⟨_, rfl⟩
    have h1 := congrArg (MvPolynomial.coeff m') (h i)
    rw [MvPolynomial.coeff_pderiv, hm', tsub_add_cancel_of_le hle] at h1
    simp only [MvPolynomial.coeff_zero] at h1
    have h2 : (((m' i : ℕ) : RatFunc F) + 1) ≠ 0 := by
      have : (((m' i : ℕ) : RatFunc F) + 1) = (((m' i + 1 : ℕ)) : RatFunc F) := by push_cast; rfl
      rw [this]; exact Nat.cast_ne_zero.2 (Nat.succ_ne_zero _)
    rw [← hm'] at h1
    exact (mul_eq_zero.1 h1).resolve_right h2

theorem lam_zero (i : Fin n) (W : MvPolynomial (Fin n) (RatFunc F)) (l : F)
    (h : MvPolynomial.pderiv i W = MvPolynomial.C (algebraMap F (RatFunc F) l) * W) :
    MvPolynomial.pderiv i W = 0 := by
  classical
  by_cases hW : W = 0
  · subst hW; simp
  by_cases hl : l = 0
  · subst hl; simp [h]
  exfalso
  have hne : W.support.Nonempty := by
    rwa [Finset.nonempty_iff_ne_empty, Ne, MvPolynomial.support_eq_empty]
  obtain ⟨m, hm, hmax⟩ := Finset.exists_max_image W.support (fun m => m i) hne
  have h1 := congrArg (MvPolynomial.coeff m) h
  rw [MvPolynomial.coeff_pderiv, MvPolynomial.coeff_C_mul] at h1
  have h2 : MvPolynomial.coeff (m + Finsupp.single i 1) W = 0 := by
    by_contra hc
    have := hmax _ (MvPolynomial.mem_support_iff.2 hc)
    simp at this
  rw [h2, zero_mul] at h1
  have h3 : MvPolynomial.coeff m W ≠ 0 := MvPolynomial.mem_support_iff.1 hm
  have h4 : algebraMap F (RatFunc F) l ≠ 0 := by simpa using hl
  exact mul_ne_zero h4 h3 h1.symm

end
end DerivationHitting.Dev.XFree

namespace DerivationHitting.Commutative
open DerivationHitting.Dev.XFree

theorem chk_wronskian_x_free {F : Type*} [Field F] [CharZero F] {n q : ℕ}
    (b : Fin n → RatFunc F) (g : Fin q → MvPolynomial (Fin n) F)
    (hclosed : derivativeClosed g) :
    ∃ a : RatFunc F, derivationWronskian b g = MvPolynomial.C a := by
  classical
  choose c hc using fun i j => (Submodule.mem_span_range_iff_exists_fun F).1 (hclosed i j)
  set E : ℕ → Fin q → MvPolynomial (Fin n) (RatFunc F) :=
    fun m j => (linearDerivation b)^[m] (rationalPolynomial (g j)) with hEdef
  have hE : ∀ (i : Fin n) (m : ℕ) (j : Fin q), MvPolynomial.pderiv i (E m j) =
      ∑ k, MvPolynomial.C (algebraMap F (RatFunc F) (c i j k)) * E m k := by
    intro i m
    induction m with
    | zero =>
      intro j
      simp only [hEdef, Function.iterate_zero, id, rationalPolynomial]
      rw [MvPolynomial.pderiv_map, ← hc i j, map_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.map_C]
    | succ m ih =>
      intro j
      have e : ∀ j, E (m + 1) j = linearDerivation b (E m j) := fun j => by
        simp only [hEdef, Function.iterate_succ_apply']
      rw [e, D_comm, ih, D_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [D_alg, e]
  have hW : derivationWronskian b g = (Matrix.of fun m j : Fin q => E m.val j).det := rfl
  have hP : ∀ i, MvPolynomial.pderiv i (derivationWronskian b g) = 0 := by
    intro i
    apply lam_zero i _ (∑ j, c i j j)
    rw [hW, deriv_det (MvPolynomial.pderiv i)]
    have : ∀ j, ((Matrix.of fun m j : Fin q => E m.val j).updateCol j
        (fun r => MvPolynomial.pderiv i ((Matrix.of fun m j : Fin q => E m.val j) r j))) =
        (Matrix.of fun m j : Fin q => E m.val j).updateCol j (fun r => ∑ k,
          MvPolynomial.C (algebraMap F (RatFunc F) (c i j k)) *
            (Matrix.of fun m j : Fin q => E m.val j) r k) := by
      intro j
      simp only [Matrix.of_apply, hE]
    have key : ∀ j, ((Matrix.of fun m j : Fin q => E m.val j).updateCol j (fun r => ∑ k,
          MvPolynomial.C (algebraMap F (RatFunc F) (c i j k)) *
            (Matrix.of fun m j : Fin q => E m.val j) r k)).det =
        MvPolynomial.C (algebraMap F (RatFunc F) (c i j j)) *
          (Matrix.of fun m j : Fin q => E m.val j).det := by
      intro j
      have := Matrix.det_updateCol_sum (Matrix.of fun m j : Fin q => E m.val j) j
        (fun k => MvPolynomial.C (algebraMap F (RatFunc F) (c i j k)))
      simpa only [smul_eq_mul] using this
    simp only [this, key]
    rw [← Finset.sum_mul, map_sum, map_sum]
  exact eq_C_of_pderiv_zero _ hP

end DerivationHitting.Commutative
end

theorem solution : type_of% @DerivationHitting.Commutative.chk_wronskian_x_free := @DerivationHitting.Commutative.chk_wronskian_x_free
