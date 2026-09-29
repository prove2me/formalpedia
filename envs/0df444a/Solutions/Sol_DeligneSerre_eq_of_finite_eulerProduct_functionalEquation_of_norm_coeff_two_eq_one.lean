-- Prove2me | solution 1 for DeligneSerre.eq_of_finite_eulerProduct_functionalEquation_of_norm_coeff_two_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/0eb0a6af-d581-5523-b822-329e3ce469c1

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_DeligneSerre_eq_of_finite_eulerProduct_functionalEquation_of_norm_coeff_two_eq_one

set_option autoImplicit false

open Polynomial Finset

namespace DeligneSerreL49G

noncomputable def eul (B : Multiset ℂ) : ℂ[X] := (B.map fun β => (1 - C β * X)).prod

noncomputable def refl (p : ℕ) (B : Multiset ℂ) : ℂ[X] := (B.map fun β => (X - C (β / (p : ℂ)))).prod

noncomputable def invRoots (P : ℂ[X]) : Multiset ℂ := P.roots.map (·⁻¹)

theorem coeff_zero_eul (B : Multiset ℂ) : (eul B).coeff 0 = 1 := by
  unfold eul
  rw [coeff_zero_multiset_prod, Multiset.map_map]
  have : (B.map ((fun f : ℂ[X] => f.coeff 0) ∘ fun β => (1 - C β * X))) = B.map fun _ => (1 : ℂ) := by
    refine Multiset.map_congr rfl fun β _ => ?_
    simp
  rw [this, Multiset.map_const', Multiset.prod_replicate, one_pow]

theorem eul_ne_zero (B : Multiset ℂ) : eul B ≠ 0 := by
  intro h
  have := coeff_zero_eul B
  rw [h, coeff_zero] at this
  exact zero_ne_one this

theorem refl_monic (p : ℕ) (B : Multiset ℂ) : (refl p B).Monic := by
  unfold refl
  exact monic_multiset_prod_of_monic _ _ fun β _ => monic_X_sub_C _

theorem refl_ne_zero (p : ℕ) (B : Multiset ℂ) : refl p B ≠ 0 := (refl_monic p B).ne_zero

theorem eval_eul (B : Multiset ℂ) (x : ℂ) :
    (eul B).eval x = (B.map fun β => 1 - β * x).prod := by
  unfold eul
  rw [eval_multiset_prod, Multiset.map_map]
  refine congrArg _ (Multiset.map_congr rfl fun β _ => ?_)
  simp

theorem eval_refl (p : ℕ) (B : Multiset ℂ) (x : ℂ) :
    (refl p B).eval x = (B.map fun β => x - β / (p : ℂ)).prod := by
  unfold refl
  rw [eval_multiset_prod, Multiset.map_map]
  refine congrArg _ (Multiset.map_congr rfl fun β _ => ?_)
  simp

theorem pow_card_mul_prod_eq_eval_refl (p : ℕ) (B : Multiset ℂ) {x : ℂ} (hx : x ≠ 0) :
    x ^ Multiset.card B * (B.map fun β => 1 - β * (x⁻¹ * (p : ℂ)⁻¹)).prod =
      (refl p B).eval x := by
  rw [eval_refl]
  induction B using Multiset.induction_on with
  | empty => simp
  | cons β B ih =>
    simp only [Multiset.card_cons, Multiset.map_cons, Multiset.prod_cons, pow_succ]
    rw [show x ^ Multiset.card B * x * ((1 - β * (x⁻¹ * (p : ℂ)⁻¹)) *
          (B.map fun β => 1 - β * (x⁻¹ * (p : ℂ)⁻¹)).prod) =
        (x * (1 - β * (x⁻¹ * (p : ℂ)⁻¹))) *
          (x ^ Multiset.card B * (B.map fun β => 1 - β * (x⁻¹ * (p : ℂ)⁻¹)).prod) by ring, ih]
    congr 1
    field_simp

theorem eq_eul_invRoots {P : ℂ[X]} (h0 : P.coeff 0 = 1) : P = eul (invRoots P) := by
  have hP : P ≠ 0 := by
    intro h; rw [h, coeff_zero] at h0; exact zero_ne_one h0
  have hroots : ∀ z ∈ P.roots, z ≠ 0 := by
    intro z hz h
    rw [mem_roots hP, h, IsRoot.def, ← coeff_zero_eq_eval_zero, h0] at hz
    exact one_ne_zero hz
  have hsplit := C_leadingCoeff_mul_prod_multiset_X_sub_C
    (IsAlgClosed.card_roots_eq_natDegree (p := P))

  have hfac : (P.roots.map fun z => X - C z).prod =
      C ((P.roots.map fun z => -z).prod) * eul (invRoots P) := by
    have : (P.roots.map fun z => X - C z) =
        P.roots.map fun z => C (-z) * (1 - C z⁻¹ * X) := by
      refine Multiset.map_congr rfl fun z hz => ?_
      have hz0 := hroots z hz
      rw [C_neg, neg_mul, mul_sub, mul_one, ← mul_assoc, ← C_mul, mul_inv_cancel₀ hz0, C_1,
        one_mul, neg_sub]
    rw [this, Multiset.prod_map_mul]
    congr 1
    · rw [Multiset.prod_hom' (s := P.roots) C fun z => -z]
    · unfold eul invRoots
      rw [Multiset.map_map]
      rfl
  rw [hfac, ← mul_assoc, ← C_mul] at hsplit

  have hconst : P.leadingCoeff * (P.roots.map fun z => -z).prod = 1 := by
    have := congrArg (fun f : ℂ[X] => f.coeff 0) hsplit
    simp only [coeff_C_mul, coeff_zero_eul, mul_one] at this
    rw [this, h0]
  rw [hconst, C_1, one_mul] at hsplit
  exact hsplit.symm

theorem mem_invRoots {P : ℂ[X]} (h0 : P.coeff 0 = 1) {β : ℂ} (hβ : β ∈ invRoots P) :
    ∃ z : ℂ, P.IsRoot z ∧ z ≠ 0 ∧ β = z⁻¹ := by
  have hP : P ≠ 0 := by
    intro h; rw [h, coeff_zero] at h0; exact zero_ne_one h0
  unfold invRoots at hβ
  rw [Multiset.mem_map] at hβ
  obtain ⟨z, hz, rfl⟩ := hβ
  rw [mem_roots hP] at hz
  refine ⟨z, hz, ?_, rfl⟩
  intro h
  rw [h, IsRoot.def, ← coeff_zero_eq_eval_zero, h0] at hz
  exact one_ne_zero hz

theorem invRoots_small {P : ℂ[X]} {p : ℕ} (h0 : P.coeff 0 = 1)
    (hP : ∀ z : ℂ, P.IsRoot z → 1 < ‖z‖ ^ 2 * p) {β : ℂ} (hβ : β ∈ invRoots P) :
    β ≠ 0 ∧ ‖β‖ ^ 2 < p := by
  obtain ⟨z, hz, hz0, rfl⟩ := mem_invRoots h0 hβ
  refine ⟨inv_ne_zero hz0, ?_⟩
  have h := hP z hz
  have hzpos : 0 < ‖z‖ ^ 2 := by positivity
  rw [norm_inv, inv_pow]
  rw [inv_lt_iff_one_lt_mul₀ hzpos]
  linarith [mul_comm (‖z‖ ^ 2) (p : ℝ)]

theorem roots_refl (p : ℕ) (B : Multiset ℂ) : (refl p B).roots = B.map (· / (p : ℂ)) := by
  unfold refl
  have : (fun β : ℂ => X - C (β / (p : ℂ))) = (fun a => X - C a) ∘ fun β => β / (p : ℂ) := rfl
  rw [this, ← Multiset.map_map, roots_multiset_prod_X_sub_C]

theorem eul_eq_C_mul_prod (B : Multiset ℂ) (hB : ∀ β ∈ B, β ≠ 0) :
    eul B = C ((B.map fun β => -β).prod) * ((B.map (·⁻¹)).map fun a => X - C a).prod := by
  unfold eul
  have : (B.map fun β => (1 - C β * X)) = B.map fun β => C (-β) * (X - C β⁻¹) := by
    refine Multiset.map_congr rfl fun β hβ => ?_
    have hβ0 := hB β hβ
    rw [C_neg, neg_mul, mul_sub, ← C_mul, mul_inv_cancel₀ hβ0, C_1]
    ring
  rw [this, Multiset.prod_map_mul, Multiset.map_map]
  congr 1
  exact Multiset.prod_hom' (s := B) C fun z => -z

theorem roots_eul (B : Multiset ℂ) (hB : ∀ β ∈ B, β ≠ 0) : (eul B).roots = B.map (·⁻¹) := by
  rw [eul_eq_C_mul_prod B hB, roots_C_mul, roots_multiset_prod_X_sub_C]
  rw [Ne, Multiset.prod_eq_zero_iff, Multiset.mem_map]
  rintro ⟨β, hβ, h⟩
  exact hB β hβ (neg_eq_zero.mp h)

section Indep

variable (S : Finset ℕ)

noncomputable def xs (s : ℂ) (p : S) : ℂ := ((p : ℕ) : ℂ) ^ (-s)

def nOf (m : S →₀ ℕ) : ℕ := ∏ p : S, (p : ℕ) ^ (m p)

variable {S}

theorem xs_ne_zero (hS : ∀ p ∈ S, p.Prime) (s : ℂ) (p : S) : xs S s p ≠ 0 := by
  unfold xs
  rw [Ne, Complex.cpow_eq_zero_iff, not_and_or]
  left
  exact_mod_cast (hS p.1 p.2).ne_zero

theorem nOf_ne_zero (hS : ∀ p ∈ S, p.Prime) (m : S →₀ ℕ) : nOf S m ≠ 0 := by
  unfold nOf
  rw [Finset.prod_ne_zero_iff]
  intro p _
  exact pow_ne_zero _ (hS p.1 p.2).ne_zero

theorem factorization_nOf (hS : ∀ p ∈ S, p.Prime) (m : S →₀ ℕ) (p : S) :
    (nOf S m).factorization p = m p := by
  unfold nOf
  rw [Nat.factorization_prod fun (q : S) _ => pow_ne_zero _ (hS q.1 q.2).ne_zero]
  simp only [Finsupp.coe_finsetSum, Finset.sum_apply, Nat.factorization_pow,
    Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_eq_single p]
  · rw [(hS p.1 p.2).factorization_self, mul_one]
  · intro q _ hqp
    rw [Nat.Prime.factorization (hS q.1 q.2), Finsupp.single_apply, if_neg, mul_zero]
    intro h
    exact hqp (Subtype.ext h)
  · intro h; exact absurd (Finset.mem_univ p) h

theorem nOf_injective (hS : ∀ p ∈ S, p.Prime) : Function.Injective (nOf S) := by
  intro m m' h
  ext p
  rw [← factorization_nOf hS m p, ← factorization_nOf hS m' p, h]

theorem natCast_pow_cpow (n k : ℕ) (z : ℂ) :
    (((n ^ k : ℕ)) : ℂ) ^ z = (((n : ℕ) : ℂ) ^ z) ^ k := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ, Nat.cast_mul, Complex.natCast_mul_natCast_cpow, ih, pow_succ]

theorem natCast_prod_cpow {ι : Type*} (T : Finset ι) (a : ι → ℕ) (z : ℂ) :
    (((∏ i ∈ T, a i : ℕ)) : ℂ) ^ z = ∏ i ∈ T, ((a i : ℕ) : ℂ) ^ z := by
  classical
  induction T using Finset.induction_on with
  | empty => simp
  | insert i T hi ih =>
    rw [Finset.prod_insert hi, Finset.prod_insert hi, Nat.cast_mul,
      Complex.natCast_mul_natCast_cpow, ih]

theorem prod_xs_pow (m : S →₀ ℕ) (s : ℂ) :
    ∏ p : S, xs S s p ^ (m p) = ((nOf S m : ℕ) : ℂ) ^ (-s) := by
  unfold nOf xs
  rw [natCast_prod_cpow]
  refine Finset.prod_congr rfl fun p _ => ?_
  rw [natCast_pow_cpow]

theorem eval_xs (F : MvPolynomial S ℂ) (s : ℂ) :
    MvPolynomial.eval (xs S s) F = ∑ m ∈ F.support, F.coeff m * ((nOf S m : ℕ) : ℂ) ^ (-s) := by
  rw [MvPolynomial.eval_eq']
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [prod_xs_pow]

noncomputable def cf (F : MvPolynomial S ℂ) (n : ℕ) : ℂ :=
  ∑ m ∈ F.support with nOf S m = n, F.coeff m

theorem cf_nOf (hS : ∀ p ∈ S, p.Prime) (F : MvPolynomial S ℂ) (m : S →₀ ℕ) :
    cf F (nOf S m) = F.coeff m := by
  classical
  unfold cf
  have : (F.support.filter fun m' => nOf S m' = nOf S m) = F.support.filter fun m' => m' = m := by
    refine Finset.filter_congr fun m' _ => ?_
    exact (nOf_injective hS).eq_iff
  rw [this, Finset.filter_eq', ]
  split_ifs with h
  · rw [Finset.sum_singleton]
  · rw [Finset.sum_empty]
    exact (MvPolynomial.notMem_support_iff.mp h).symm

theorem cf_eq_zero_of_notMem (F : MvPolynomial S ℂ) {n : ℕ}
    (hn : n ∉ F.support.image (nOf S)) : cf F n = 0 := by
  unfold cf
  refine Finset.sum_eq_zero fun m hm => ?_
  rw [Finset.mem_filter] at hm
  exact absurd (Finset.mem_image.mpr ⟨m, hm.1, hm.2⟩) hn

theorem norm_cf_le (F : MvPolynomial S ℂ) (n : ℕ) :
    ‖cf F n‖ ≤ ∑ m ∈ F.support, ‖F.coeff m‖ := by
  unfold cf
  refine (norm_sum_le _ _).trans ?_
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun _ _ _ => norm_nonneg _

theorem LSeries_cf (hS : ∀ p ∈ S, p.Prime) (F : MvPolynomial S ℂ) (s : ℂ) :
    LSeries (cf F) s = MvPolynomial.eval (xs S s) F := by
  classical
  rw [eval_xs, LSeries]
  rw [tsum_eq_sum (s := F.support.image (nOf S))]
  · refine Finset.sum_image' _ fun m _ => ?_

    rw [LSeries.term_of_ne_zero (nOf_ne_zero hS m), cf, Finset.sum_div]
    refine Finset.sum_congr rfl fun m' hm' => ?_
    rw [Finset.mem_filter] at hm'
    rw [hm'.2, div_eq_mul_inv, ← Complex.cpow_neg]
  · intro n hn
    rw [LSeries.term]
    split_ifs with h0
    · rfl
    · rw [cf_eq_zero_of_notMem F hn, zero_div]

theorem abscissaOfAbsConv_cf_lt_top (F : MvPolynomial S ℂ) :
    LSeries.abscissaOfAbsConv (cf F) < ⊤ := by
  have hsum : LSeriesSummable (cf F) (2 : ℝ) :=
    LSeriesSummable_of_bounded_of_one_lt_real (m := ∑ m ∈ F.support, ‖F.coeff m‖)
      (fun n _ => norm_cf_le F n) (by norm_num)
  exact lt_of_le_of_lt hsum.abscissaOfAbsConv_le (EReal.coe_lt_top _)

theorem eq_of_eval_xs_eq (hS : ∀ p ∈ S, p.Prime) {F G : MvPolynomial S ℂ}
    (h : ∀ᶠ s : ℝ in Filter.atTop, MvPolynomial.eval (xs S s) F = MvPolynomial.eval (xs S s) G) :
    F = G := by
  have hL : (fun x : ℝ => LSeries (cf F) x) =ᶠ[Filter.atTop] fun x => LSeries (cf G) x :=
    h.mono fun x hx => by
      show LSeries (cf F) x = LSeries (cf G) x
      rw [LSeries_cf hS, LSeries_cf hS, hx]
  have hcf : ∀ n ≠ 0, cf F n = cf G n := fun n hn =>
    LSeries.eq_of_LSeries_eventually_eq (abscissaOfAbsConv_cf_lt_top F)
      (abscissaOfAbsConv_cf_lt_top G) hL hn
  ext m
  rw [← cf_nOf hS F m, ← cf_nOf hS G m]
  exact hcf _ (nOf_ne_zero hS m)

end Indep

noncomputable def Lpoly (p : ℕ) (e : ℤ) (B' Cm C' : Multiset ℂ) : ℂ[X] :=
  X ^ (2 * e.toNat + Multiset.card C') * refl p B' * eul Cm

noncomputable def Rpoly (p : ℕ) (e : ℤ) (B B' C' : Multiset ℂ) : ℂ[X] :=
  X ^ (e.toNat + (-e).toNat + Multiset.card B') * eul B * refl p C'

def Dexp (e : ℤ) (B' C' : Multiset ℂ) : ℕ := e.toNat + (-e).toNat + Multiset.card B' + Multiset.card C'

theorem Lpoly_ne_zero (p : ℕ) (e : ℤ) (B' Cm C' : Multiset ℂ) : Lpoly p e B' Cm C' ≠ 0 :=
  mul_ne_zero (mul_ne_zero (pow_ne_zero _ X_ne_zero) (refl_ne_zero p B')) (eul_ne_zero Cm)

theorem Rpoly_ne_zero (p : ℕ) (e : ℤ) (B B' C' : Multiset ℂ) : Rpoly p e B B' C' ≠ 0 :=
  mul_ne_zero (mul_ne_zero (pow_ne_zero _ X_ne_zero) (eul_ne_zero B)) (refl_ne_zero p C')

theorem toNat_add_toNat_neg_eq (e : ℤ) :
    ((e.toNat + (-e).toNat + e.toNat + (-e).toNat : ℕ) : ℤ) + 0 =
      ((e.toNat + (-e).toNat : ℕ) : ℤ) + (e.toNat + (-e).toNat : ℕ) := by push_cast; ring

theorem key_left (p : ℕ) (e : ℤ) (B' Cm C' : Multiset ℂ) {x : ℂ} (hx : x ≠ 0) :
    x ^ Dexp e B' C' * (x ^ e * (B'.map fun β => 1 - β * (x⁻¹ * (p : ℂ)⁻¹)).prod *
        (Cm.map fun γ => 1 - γ * x).prod) =
      (Lpoly p e B' Cm C').eval x := by
  unfold Lpoly Dexp
  rw [eval_mul, eval_mul, eval_pow, eval_X, eval_eul, ← pow_card_mul_prod_eq_eval_refl p B' hx]
  have hpow : x ^ (e.toNat + (-e).toNat + Multiset.card B' + Multiset.card C') * x ^ e =
      x ^ (2 * e.toNat + Multiset.card C') * x ^ Multiset.card B' := by
    rw [← zpow_natCast, ← zpow_add₀ hx, ← pow_add, ← zpow_natCast]
    congr 1
    have he : ((e.toNat : ℕ) : ℤ) - (((-e).toNat : ℕ) : ℤ) = e := Int.toNat_sub_toNat_neg e
    push_cast
    omega
  calc x ^ (e.toNat + (-e).toNat + Multiset.card B' + Multiset.card C') *
        (x ^ e * (B'.map fun β => 1 - β * (x⁻¹ * (p : ℂ)⁻¹)).prod *
          (Cm.map fun γ => 1 - γ * x).prod)
      = (x ^ (e.toNat + (-e).toNat + Multiset.card B' + Multiset.card C') * x ^ e) *
          (B'.map fun β => 1 - β * (x⁻¹ * (p : ℂ)⁻¹)).prod *
            (Cm.map fun γ => 1 - γ * x).prod := by ring
    _ = x ^ (2 * e.toNat + Multiset.card C') * x ^ Multiset.card B' *
          (B'.map fun β => 1 - β * (x⁻¹ * (p : ℂ)⁻¹)).prod *
            (Cm.map fun γ => 1 - γ * x).prod := by rw [hpow]
    _ = _ := by ring

theorem key_right (p : ℕ) (e : ℤ) (B B' C' : Multiset ℂ) {x : ℂ} (hx : x ≠ 0) :
    x ^ Dexp e B' C' * ((B.map fun β => 1 - β * x).prod *
        (C'.map fun γ => 1 - γ * (x⁻¹ * (p : ℂ)⁻¹)).prod) =
      (Rpoly p e B B' C').eval x := by
  unfold Rpoly Dexp
  rw [eval_mul, eval_mul, eval_pow, eval_X, eval_eul, ← pow_card_mul_prod_eq_eval_refl p C' hx,
    pow_add]
  ring

theorem cpow_sub_one_eq {p : ℕ} (hp : p ≠ 0) (s : ℂ) :
    (p : ℂ) ^ (s - 1) = ((p : ℂ) ^ (-s))⁻¹ * (p : ℂ)⁻¹ := by
  have hp' : (p : ℂ) ≠ 0 := by exact_mod_cast hp
  rw [Complex.cpow_sub _ _ hp', Complex.cpow_one, Complex.cpow_neg, inv_inv, div_eq_mul_inv]

section MvEval

variable {σ : Type*}

theorem eval_aeval_X (g : σ → ℂ) (i : σ) (f : ℂ[X]) :
    MvPolynomial.eval g (Polynomial.aeval (MvPolynomial.X i : MvPolynomial σ ℂ) f) =
      f.eval (g i) := by
  have h := Polynomial.aeval_algHom_apply (MvPolynomial.aeval g)
    (MvPolynomial.X i : MvPolynomial σ ℂ) f
  rw [MvPolynomial.aeval_X] at h
  rw [← MvPolynomial.aeval_eq_eval]
  change (MvPolynomial.aeval g) (Polynomial.aeval (MvPolynomial.X i : MvPolynomial σ ℂ) f) = _
  rw [← h, ← Polynomial.coe_aeval_eq_eval]

noncomputable def spec [DecidableEq σ] (i : σ) (t : ℂ) : MvPolynomial σ ℂ →ₐ[ℂ] ℂ[X] :=
  MvPolynomial.aeval fun j => if j = i then (Polynomial.X : ℂ[X]) else Polynomial.C t

theorem spec_aeval_X_self [DecidableEq σ] (i : σ) (t : ℂ) (f : ℂ[X]) :
    spec i t (Polynomial.aeval (MvPolynomial.X i : MvPolynomial σ ℂ) f) = f := by
  have h := Polynomial.aeval_algHom_apply (spec i t) (MvPolynomial.X i : MvPolynomial σ ℂ) f
  rw [← h]
  unfold spec
  rw [MvPolynomial.aeval_X, if_pos rfl, aeval_X_left_apply]

theorem spec_aeval_X_ne [DecidableEq σ] {i j : σ} (hji : j ≠ i) (t : ℂ) (f : ℂ[X]) :
    spec i t (Polynomial.aeval (MvPolynomial.X j : MvPolynomial σ ℂ) f) =
      Polynomial.C (f.eval t) := by
  have h := Polynomial.aeval_algHom_apply (spec i t) (MvPolynomial.X j : MvPolynomial σ ℂ) f
  rw [← h]
  unfold spec
  rw [MvPolynomial.aeval_X, if_neg hji, C_eq_algebraMap t, aeval_algebraMap_apply_eq_algebraMap_eval]
  rfl

theorem spec_prod [DecidableEq σ] (T : Finset σ) {i : σ} (hi : i ∈ T) (t : ℂ) (f : σ → ℂ[X]) :
    spec i t (∏ j ∈ T, Polynomial.aeval (MvPolynomial.X j : MvPolynomial σ ℂ) (f j)) =
      f i * Polynomial.C (∏ j ∈ T.erase i, (f j).eval t) := by
  rw [map_prod, ← Finset.mul_prod_erase T _ hi, spec_aeval_X_self]
  congr 1
  rw [map_prod]
  refine Finset.prod_congr rfl fun j hj => ?_
  rw [Finset.mem_erase] at hj
  exact spec_aeval_X_ne hj.1 t (f j)

end MvEval

def SmallRt (p : ℕ) (z : ℂ) : Prop := ‖z‖ ^ 2 * p < 1

noncomputable scoped instance (p : ℕ) : DecidablePred (SmallRt p) := fun _ => by unfold SmallRt; infer_instance

theorem small_zero (p : ℕ) : SmallRt p 0 := by simp [SmallRt]

theorem small_div {p : ℕ} (hp : p ≠ 0) {β : ℂ} (hβ : ‖β‖ ^ 2 < p) : SmallRt p (β / (p : ℂ)) := by
  unfold SmallRt
  have hp' : (0 : ℝ) < p := by exact_mod_cast Nat.pos_of_ne_zero hp
  rw [norm_div, Complex.norm_natCast, div_pow]
  rw [div_mul_eq_mul_div, div_lt_one (by positivity)]
  nlinarith

theorem not_small_inv {p : ℕ} {γ : ℂ} (hγ0 : γ ≠ 0) (hγ : ‖γ‖ ^ 2 < p) : ¬ SmallRt p γ⁻¹ := by
  unfold SmallRt
  rw [norm_inv, inv_pow, not_lt]
  have hpos : 0 < ‖γ‖ ^ 2 := by positivity
  rw [le_inv_mul_iff₀ hpos, mul_one]
  exact hγ.le

theorem roots_Lpoly (p : ℕ) (e : ℤ) (B' Cm C' : Multiset ℂ) (hCm : ∀ γ ∈ Cm, γ ≠ 0) :
    (Lpoly p e B' Cm C').roots =
      (2 * e.toNat + Multiset.card C') • ({0} : Multiset ℂ) + B'.map (· / (p : ℂ)) +
        Cm.map (·⁻¹) := by
  unfold Lpoly
  rw [roots_mul (Lpoly_ne_zero p e B' Cm C'), roots_mul, roots_X_pow, roots_refl, roots_eul Cm hCm]
  exact mul_ne_zero (pow_ne_zero _ X_ne_zero) (refl_ne_zero p B')

theorem roots_Rpoly (p : ℕ) (e : ℤ) (B B' C' : Multiset ℂ) (hB : ∀ β ∈ B, β ≠ 0) :
    (Rpoly p e B B' C').roots =
      (e.toNat + (-e).toNat + Multiset.card B') • ({0} : Multiset ℂ) + B.map (·⁻¹) +
        C'.map (· / (p : ℂ)) := by
  unfold Rpoly
  rw [roots_mul (Rpoly_ne_zero p e B B' C'), roots_mul, roots_X_pow, roots_eul B hB, roots_refl]
  exact mul_ne_zero (pow_ne_zero _ X_ne_zero) (eul_ne_zero B)

theorem filter_small_map_div {p : ℕ} (hp : p ≠ 0) (B : Multiset ℂ) (hB : ∀ β ∈ B, ‖β‖ ^ 2 < p) :
    (B.map (· / (p : ℂ))).filter (SmallRt p) = B.map (· / (p : ℂ)) := by
  rw [Multiset.filter_eq_self]
  intro z hz
  rw [Multiset.mem_map] at hz
  obtain ⟨β, hβ, rfl⟩ := hz
  exact small_div hp (hB β hβ)

theorem filter_small_map_inv {p : ℕ} (B : Multiset ℂ) (hB : ∀ β ∈ B, β ≠ 0 ∧ ‖β‖ ^ 2 < p) :
    (B.map (·⁻¹)).filter (SmallRt p) = 0 := by
  rw [Multiset.filter_eq_nil]
  intro z hz
  rw [Multiset.mem_map] at hz
  obtain ⟨β, hβ, rfl⟩ := hz
  exact not_small_inv (hB β hβ).1 (hB β hβ).2

theorem filter_not_small_map_div {p : ℕ} (hp : p ≠ 0) (B : Multiset ℂ)
    (hB : ∀ β ∈ B, ‖β‖ ^ 2 < p) :
    (B.map (· / (p : ℂ))).filter (fun z => ¬ SmallRt p z) = 0 := by
  rw [Multiset.filter_eq_nil]
  intro z hz
  rw [Multiset.mem_map] at hz
  obtain ⟨β, hβ, rfl⟩ := hz
  exact not_not_intro (small_div hp (hB β hβ))

theorem filter_not_small_map_inv {p : ℕ} (B : Multiset ℂ)
    (hB : ∀ β ∈ B, β ≠ 0 ∧ ‖β‖ ^ 2 < p) :
    (B.map (·⁻¹)).filter (fun z => ¬ SmallRt p z) = B.map (·⁻¹) := by
  rw [Multiset.filter_eq_self]
  intro z hz
  rw [Multiset.mem_map] at hz
  obtain ⟨β, hβ, rfl⟩ := hz
  exact not_small_inv (hB β hβ).1 (hB β hβ).2

theorem filter_ne_zero_map_div {p : ℕ} (hp : p ≠ 0) (B : Multiset ℂ) (hB : ∀ β ∈ B, β ≠ 0) :
    (B.map (· / (p : ℂ))).filter (· ≠ 0) = B.map (· / (p : ℂ)) := by
  rw [Multiset.filter_eq_self]
  intro z hz
  rw [Multiset.mem_map] at hz
  obtain ⟨β, hβ, rfl⟩ := hz
  have hp' : (p : ℂ) ≠ 0 := by exact_mod_cast hp
  exact div_ne_zero (hB β hβ) hp'

theorem one_prime {p : ℕ} (hp : p ≠ 0) (e : ℤ) (B Cm B' C' : Multiset ℂ)
    (hB : ∀ β ∈ B, β ≠ 0 ∧ ‖β‖ ^ 2 < p) (hCm : ∀ β ∈ Cm, β ≠ 0 ∧ ‖β‖ ^ 2 < p)
    (hB' : ∀ β ∈ B', β ≠ 0 ∧ ‖β‖ ^ 2 < p) (hC' : ∀ β ∈ C', β ≠ 0 ∧ ‖β‖ ^ 2 < p)
    {c₁ c₂ : ℂ} (hc₁ : c₁ ≠ 0) (hc₂ : c₂ ≠ 0)
    (h : Polynomial.C c₁ * Lpoly p e B' Cm C' = Polynomial.C c₂ * Rpoly p e B B' C') :
    e = 0 ∧ B = Cm ∧ B' = C' := by
  have hp' : (p : ℂ) ≠ 0 := by exact_mod_cast hp
  have hroots := congrArg Polynomial.roots h
  rw [roots_C_mul _ hc₁, roots_C_mul _ hc₂, roots_Lpoly p e B' Cm C' (fun γ hγ => (hCm γ hγ).1),
    roots_Rpoly p e B B' C' (fun β hβ => (hB β hβ).1)] at hroots

  have hsmall := congrArg (Multiset.filter (SmallRt p)) hroots
  simp only [Multiset.filter_add, Multiset.filter_nsmul,
    Multiset.filter_singleton, small_zero, if_true,
    filter_small_map_div hp B' (fun β hβ => (hB' β hβ).2),
    filter_small_map_div hp C' (fun β hβ => (hC' β hβ).2),
    filter_small_map_inv Cm hCm, filter_small_map_inv B hB, add_zero] at hsmall

  have hlarge := congrArg (Multiset.filter fun z => ¬ SmallRt p z) hroots
  simp only [Multiset.filter_add, Multiset.filter_nsmul,
    Multiset.filter_singleton, small_zero, not_true_eq_false, if_false, Multiset.empty_eq_zero,
    smul_zero, zero_add,
    filter_not_small_map_div hp B' (fun β hβ => (hB' β hβ).2),
    filter_not_small_map_div hp C' (fun β hβ => (hC' β hβ).2),
    filter_not_small_map_inv Cm hCm, filter_not_small_map_inv B hB, add_zero] at hlarge
  have hBCm : B = Cm := by
    have := Multiset.map_injective inv_injective hlarge
    exact this.symm

  have hnz := congrArg (Multiset.filter (· ≠ 0)) hsmall
  simp only [Multiset.filter_add, Multiset.filter_nsmul, Multiset.filter_singleton,
    ne_eq, not_true_eq_false, if_false, Multiset.empty_eq_zero, smul_zero, zero_add] at hnz
  rw [filter_ne_zero_map_div hp B' (fun β hβ => (hB' β hβ).1),
    filter_ne_zero_map_div hp C' (fun β hβ => (hC' β hβ).1)] at hnz
  have hB'C' : B' = C' := by
    refine Multiset.map_injective (f := fun x : ℂ => x / (p : ℂ)) ?_ hnz
    simpa only [div_eq_mul_inv] using mul_left_injective₀ (inv_ne_zero hp')
  refine ⟨?_, hBCm, hB'C'⟩

  have hcount := congrArg (Multiset.count (0 : ℂ)) hsmall
  rw [hB'C'] at hcount
  simp only [Multiset.count_add, Multiset.count_nsmul, Multiset.count_singleton_self, mul_one,
    Nat.add_right_cancel_iff] at hcount
  have he : ((e.toNat : ℕ) : ℤ) - (((-e).toNat : ℕ) : ℤ) = e := Int.toNat_sub_toNat_neg e
  omega

theorem prod_map_neg_ne_zero (B : Multiset ℂ) (hB : ∀ β ∈ B, β ≠ 0) :
    (B.map fun β => -β).prod ≠ 0 := by
  rw [Ne, Multiset.prod_eq_zero_iff, Multiset.mem_map]
  rintro ⟨β, hβ, h⟩
  exact hB β hβ (neg_eq_zero.mp h)

theorem natDegree_eul (B : Multiset ℂ) (hB : ∀ β ∈ B, β ≠ 0) :
    (eul B).natDegree = Multiset.card B := by
  rw [eul_eq_C_mul_prod B hB, natDegree_C_mul (prod_map_neg_ne_zero B hB),
    natDegree_multiset_prod_X_sub_C_eq_card, Multiset.card_map]

theorem coeff_card_eul (B : Multiset ℂ) (hB : ∀ β ∈ B, β ≠ 0) :
    (eul B).coeff (Multiset.card B) = (B.map fun β => -β).prod := by
  rw [eul_eq_C_mul_prod B hB, coeff_C_mul]
  have hmonic : ((B.map (·⁻¹)).map fun a => X - C a).prod.Monic :=
    monic_multiset_prod_of_monic _ _ fun a _ => monic_X_sub_C a
  have hdeg : ((B.map (·⁻¹)).map fun a => X - C a).prod.natDegree = Multiset.card B := by
    rw [natDegree_multiset_prod_X_sub_C_eq_card, Multiset.card_map]
  rw [← hdeg, hmonic.coeff_natDegree, mul_one]

theorem exists_pair_of_norm_coeff_two (Cm : Multiset ℂ) (hCm : ∀ γ ∈ Cm, γ ≠ 0)
    (hdeg : (eul Cm).natDegree ≤ 2) (hcoeff : ‖(eul Cm).coeff 2‖ = 1) :
    ∃ l m : ℂ, Cm = {l, m} ∧ ‖l‖ * ‖m‖ = 1 := by
  have hcard : Multiset.card Cm = 2 := by
    rw [natDegree_eul Cm hCm] at hdeg
    rcases Nat.lt_or_ge (Multiset.card Cm) 2 with h | h
    · exfalso
      have : (eul Cm).coeff 2 = 0 :=
        coeff_eq_zero_of_natDegree_lt (by rw [natDegree_eul Cm hCm]; exact h)
      rw [this, norm_zero] at hcoeff
      exact zero_ne_one hcoeff
    · exact le_antisymm hdeg h
  obtain ⟨l, m, hlm⟩ := Multiset.card_eq_two.mp hcard
  refine ⟨l, m, hlm, ?_⟩
  have h2 := coeff_card_eul Cm hCm
  rw [hcard] at h2
  rw [h2, hlm, Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton,
    Multiset.prod_cons, Multiset.prod_singleton, neg_mul_neg, norm_mul] at hcoeff
  exact hcoeff

theorem norm_invRoots_eq_one {P : ℂ[X]} (h0 : P.coeff 0 = 1)
    (hP : ∀ z : ℂ, P.IsRoot z → ‖z‖ = 1) {β : ℂ} (hβ : β ∈ invRoots P) : ‖β‖ = 1 := by
  obtain ⟨z, hz, -, rfl⟩ := mem_invRoots h0 hβ
  rw [norm_inv, hP z hz, inv_one]

theorem small_of_norm_eq_one {p : ℕ} (hp : 2 ≤ p) {β : ℂ} (h : ‖β‖ = 1) :
    β ≠ 0 ∧ ‖β‖ ^ 2 < p := by
  refine ⟨fun hβ => ?_, ?_⟩
  · rw [hβ, norm_zero] at h; exact zero_ne_one h
  · rw [h, one_pow]; exact_mod_cast hp

theorem core_real {P x y x' y' : ℝ} (hP : 2 ≤ P) (hx : 0 < x) (hy : 0 < y) (hx' : 0 < x')
    (hy' : 0 < y') (hxy : x * y = 1) (hxy' : x' * y' = 1)
    (F1 : y = 1 ∨ y = x' / P ∨ y = y' / P)
    (F2 : x = 1 ∨ x = x' / P ∨ x = y' / P)
    (F3 : x' = 1 ∨ x' / P = y ∨ x' / P = x)
    (F4 : y' = 1 ∨ y' / P = y ∨ y' / P = x) :
    x = 1 ∧ y = 1 ∧ x' = 1 ∧ y' = 1 := by
  have hP0 : 0 < P := by linarith

  have F1' : y = 1 ∨ P * y = x' ∨ P * y = y' := by
    rcases F1 with h | h | h
    · exact Or.inl h
    · right; left; rw [h]; field_simp
    · right; right; rw [h]; field_simp
  have F2' : x = 1 ∨ P * x = x' ∨ P * x = y' := by
    rcases F2 with h | h | h
    · exact Or.inl h
    · right; left; rw [h]; field_simp
    · right; right; rw [h]; field_simp
  have F3' : x' = 1 ∨ x' = P * y ∨ x' = P * x := by
    rcases F3 with h | h | h
    · exact Or.inl h
    · right; left; rw [← h]; field_simp
    · right; right; rw [← h]; field_simp
  have F4' : y' = 1 ∨ y' = P * y ∨ y' = P * x := by
    rcases F4 with h | h | h
    · exact Or.inl h
    · right; left; rw [← h]; field_simp
    · right; right; rw [← h]; field_simp
  clear F1 F2 F3 F4

  have hxy1 : x = 1 ∧ y = 1 := by
    rcases F2' with h2 | h2 | h2
    · refine ⟨h2, ?_⟩
      rw [h2, one_mul] at hxy; exact hxy
    ·
      exfalso
      rcases F4' with h4 | h4 | h4
      ·
        have hx'1 : x' = 1 := by rw [h4, mul_one] at hxy'; exact hxy'
        rcases F1' with h1 | h1 | h1 <;> nlinarith
      ·
        have : x' * y' = P ^ 2 * (x * y) := by rw [← h2, h4]; ring
        rw [hxy, hxy', mul_one] at this
        nlinarith
      ·
        have hx'y' : x' = y' := by rw [h4, ← h2]
        have hx'1 : x' = 1 := by nlinarith
        rcases F1' with h1 | h1 | h1 <;> nlinarith
    ·
      exfalso
      rcases F3' with h3 | h3 | h3
      · have hy'1 : y' = 1 := by rw [h3, one_mul] at hxy'; exact hxy'
        rcases F1' with h1 | h1 | h1 <;> nlinarith
      · have : x' * y' = P ^ 2 * (x * y) := by rw [← h2, h3]; ring
        rw [hxy, hxy', mul_one] at this
        nlinarith
      · have hx'y' : x' = y' := by rw [h3, ← h2]
        have hy'1 : y' = 1 := by nlinarith
        rcases F1' with h1 | h1 | h1 <;> nlinarith
  obtain ⟨hx1, hy1⟩ := hxy1
  subst hx1; subst hy1
  refine ⟨rfl, rfl, ?_⟩

  rcases F3' with h3 | h3 | h3
  · refine ⟨h3, ?_⟩
    rw [h3, one_mul] at hxy'; exact hxy'
  · exfalso
    rw [mul_one] at h3
    rcases F4' with h4 | h4 | h4 <;> nlinarith
  · exfalso
    rw [mul_one] at h3
    rcases F4' with h4 | h4 | h4 <;> nlinarith

theorem mem_roots_shape {a : ℕ} {U V : Multiset ℂ} {f g : ℂ → ℂ} {z : ℂ} :
    z ∈ a • ({0} : Multiset ℂ) + U.map f + V.map g ↔
      (a ≠ 0 ∧ z = 0) ∨ (∃ u ∈ U, f u = z) ∨ ∃ v ∈ V, g v = z := by
  simp only [Multiset.mem_add, Multiset.mem_nsmul, Multiset.mem_singleton, Multiset.mem_map,
    or_assoc]

theorem norm_eq_one_of_roots_eq {p : ℕ} (hp : 2 ≤ p) (a b : ℕ) (B B' Cm C' : Multiset ℂ)
    (hB : ∀ β ∈ B, ‖β‖ = 1) (hB' : ∀ β ∈ B', ‖β‖ = 1)
    {l m l' m' : ℂ} (hCm : Cm = {l, m}) (hlm : ‖l‖ * ‖m‖ = 1)
    (hC' : C' = {l', m'}) (hlm' : ‖l'‖ * ‖m'‖ = 1)
    (h : a • ({0} : Multiset ℂ) + B'.map (· / (p : ℂ)) + Cm.map (·⁻¹) =
      b • ({0} : Multiset ℂ) + B.map (·⁻¹) + C'.map (· / (p : ℂ))) :
    (∀ γ ∈ Cm, ‖γ‖ = 1) ∧ ∀ γ ∈ C', ‖γ‖ = 1 := by
  have hP : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast (show p ≠ 0 by omega)
  have hpn : ‖(p : ℂ)‖ = (p : ℝ) := Complex.norm_natCast p

  have hl : 0 < ‖l‖ := by
    rcases (norm_nonneg l).lt_or_eq with h | h
    · exact h
    · rw [← h, zero_mul] at hlm; exact absurd hlm zero_ne_one
  have hm : 0 < ‖m‖ := by
    rcases (norm_nonneg m).lt_or_eq with h | h
    · exact h
    · rw [← h, mul_zero] at hlm; exact absurd hlm zero_ne_one
  have hl' : 0 < ‖l'‖ := by
    rcases (norm_nonneg l').lt_or_eq with h | h
    · exact h
    · rw [← h, zero_mul] at hlm'; exact absurd hlm' zero_ne_one
  have hm' : 0 < ‖m'‖ := by
    rcases (norm_nonneg m').lt_or_eq with h | h
    · exact h
    · rw [← h, mul_zero] at hlm'; exact absurd hlm' zero_ne_one
  have hl0 : l ≠ 0 := norm_pos_iff.mp hl
  have hm0 : m ≠ 0 := norm_pos_iff.mp hm
  have hl'0 : l' ≠ 0 := norm_pos_iff.mp hl'
  have hm'0 : m' ≠ 0 := norm_pos_iff.mp hm'

  have hLR : ∀ z, z ∈ a • ({0} : Multiset ℂ) + B'.map (· / (p : ℂ)) + Cm.map (·⁻¹) →
      z ∈ b • ({0} : Multiset ℂ) + B.map (·⁻¹) + C'.map (· / (p : ℂ)) := fun z hz => h ▸ hz
  have hRL : ∀ z, z ∈ b • ({0} : Multiset ℂ) + B.map (·⁻¹) + C'.map (· / (p : ℂ)) →
      z ∈ a • ({0} : Multiset ℂ) + B'.map (· / (p : ℂ)) + Cm.map (·⁻¹) := fun z hz => h ▸ hz

  have hCmem : ∀ γ ∈ Cm, γ ≠ 0 →
      ‖γ‖⁻¹ = 1 ∨ ‖γ‖⁻¹ = ‖l'‖ / p ∨ ‖γ‖⁻¹ = ‖m'‖ / p := by
    intro γ hγ hγ0
    have hz := hLR γ⁻¹ (mem_roots_shape.mpr (Or.inr (Or.inr ⟨γ, hγ, rfl⟩)))
    rcases mem_roots_shape.mp hz with ⟨-, h0⟩ | ⟨β, hβ, hβe⟩ | ⟨γ', hγ', hγ'e⟩
    · exact absurd h0 (inv_ne_zero hγ0)
    · left
      rw [← norm_inv, ← hβe, norm_inv, hB β hβ, inv_one]
    · right
      rw [← norm_inv, ← hγ'e, norm_div, hpn]
      rw [hC', Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at hγ'
      rcases hγ' with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr rfl

  have hC'mem : ∀ γ' ∈ C', ‖γ'‖ = 1 ∨ ‖γ'‖ / p = ‖l‖⁻¹ ∨ ‖γ'‖ / p = ‖m‖⁻¹ := by
    intro γ' hγ'
    have hz := hRL (γ' / (p : ℂ)) (mem_roots_shape.mpr (Or.inr (Or.inr ⟨γ', hγ', rfl⟩)))
    rcases mem_roots_shape.mp hz with ⟨-, h0⟩ | ⟨β, hβ, hβe⟩ | ⟨γ, hγ, hγe⟩
    · exfalso
      rw [hC', Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at hγ'
      rcases hγ' with rfl | rfl
      · exact hl'0 ((div_eq_zero_iff.mp h0).resolve_right hp0)
      · exact hm'0 ((div_eq_zero_iff.mp h0).resolve_right hp0)
    · left
      have := congrArg (fun w : ℂ => ‖w‖) hβe
      simp only [norm_div, hpn, hB' β hβ] at this
      have hp' : (0 : ℝ) < p := by linarith
      field_simp at this
      linarith
    · right
      have hn : ‖γ'‖ / p = ‖γ‖⁻¹ := by rw [← norm_inv, hγe, norm_div, hpn]
      rw [hn]
      rw [hCm, Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at hγ
      rcases hγ with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr rfl

  have hml : ‖l‖⁻¹ = ‖m‖ := (eq_inv_of_mul_eq_one_right hlm).symm
  have hlm2 : ‖m‖⁻¹ = ‖l‖ := (eq_inv_of_mul_eq_one_left hlm).symm
  have F1 := hCmem l (by rw [hCm]; exact Multiset.mem_cons_self _ _) hl0
  have F2 := hCmem m (by rw [hCm, Multiset.insert_eq_cons]; exact
    Multiset.mem_cons_of_mem (Multiset.mem_singleton_self _)) hm0
  have F3 := hC'mem l' (by rw [hC']; exact Multiset.mem_cons_self _ _)
  have F4 := hC'mem m' (by rw [hC', Multiset.insert_eq_cons]; exact
    Multiset.mem_cons_of_mem (Multiset.mem_singleton_self _))
  rw [hml] at F1 F3 F4
  rw [hlm2] at F2 F3 F4
  obtain ⟨hx, hy, hx', hy'⟩ := core_real hP hl hm hl' hm' hlm hlm' F1 F2 F3 F4
  constructor
  · intro γ hγ
    rw [hCm, Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at hγ
    rcases hγ with rfl | rfl
    · exact hx
    · exact hy
  · intro γ hγ
    rw [hC', Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at hγ
    rcases hγ with rfl | rfl
    · exact hx'
    · exact hy'

section Assembly

variable {S : Finset ℕ}

theorem exists_eval_ne_zero (T : Finset ℕ) (f : ℕ → ℂ[X]) (hf : ∀ q ∈ T, f q ≠ 0) :
    ∃ t : ℂ, ∀ q ∈ T, (f q).eval t ≠ 0 := by
  have hprod : ∏ q ∈ T, f q ≠ 0 := Finset.prod_ne_zero_iff.mpr hf
  obtain ⟨t, ht⟩ := Infinite.exists_notMem_finset (∏ q ∈ T, f q).roots.toFinset
  refine ⟨t, fun q hq h => ht ?_⟩
  rw [Multiset.mem_toFinset, mem_roots hprod, IsRoot.def, eval_prod]
  exact Finset.prod_eq_zero hq h

end Assembly

end DeligneSerreL49G
p2m_reactivate "P2MW.S_DeligneSerre_eq_of_finite_eulerProduct_functionalEquation_of_norm_coeff_two_eq_one.DeligneSerreL49G"

open DeligneSerreL49G in

theorem solution
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) (e : ℕ → ℤ) (ω : ℂ) (hω : ω ≠ 0)
    (P Q P' Q' : ℕ → ℂ[X])
    (hP₀ : ∀ p ∈ S, (P p).coeff 0 = 1) (hQ₀ : ∀ p ∈ S, (Q p).coeff 0 = 1)
    (hP'₀ : ∀ p ∈ S, (P' p).coeff 0 = 1) (hQ'₀ : ∀ p ∈ S, (Q' p).coeff 0 = 1)
    (hP : ∀ p ∈ S, ∀ z : ℂ, (P p).IsRoot z → 1 < ‖z‖ ^ 2 * p)
    (hP' : ∀ p ∈ S, ∀ z : ℂ, (P' p).IsRoot z → 1 < ‖z‖ ^ 2 * p)
    (hQ : ∀ p ∈ S,
      ((∀ z : ℂ, (Q p).IsRoot z → 1 < ‖z‖ ^ 2 * p) ∧
          ∀ z : ℂ, (Q' p).IsRoot z → 1 < ‖z‖ ^ 2 * p) ∨
        ((∀ z : ℂ, (P p).IsRoot z → ‖z‖ = 1) ∧ (∀ z : ℂ, (P' p).IsRoot z → ‖z‖ = 1) ∧
          (Q p).natDegree ≤ 2 ∧ ‖(Q p).coeff 2‖ = 1 ∧
          (Q' p).natDegree ≤ 2 ∧ ‖(Q' p).coeff 2‖ = 1))
    (σ₀ : ℝ)
    (hFE : ∀ s : ℝ, σ₀ ≤ s →
      (∏ p ∈ S, ((p : ℂ) ^ (-(s : ℂ))) ^ (e p)) *
          ∏ p ∈ S, (P' p).eval ((p : ℂ) ^ ((s : ℂ) - 1)) * (Q p).eval ((p : ℂ) ^ (-(s : ℂ))) =
        ω * ∏ p ∈ S, (P p).eval ((p : ℂ) ^ (-(s : ℂ))) * (Q' p).eval ((p : ℂ) ^ ((s : ℂ) - 1))) :
    ∀ p ∈ S, e p = 0 ∧ P p = Q p ∧ P' p = Q' p := by
  classical

  set B : ℕ → Multiset ℂ := fun p => invRoots (P p) with hBdef
  set Cm : ℕ → Multiset ℂ := fun p => invRoots (Q p) with hCmdef
  set B' : ℕ → Multiset ℂ := fun p => invRoots (P' p) with hB'def
  set C' : ℕ → Multiset ℂ := fun p => invRoots (Q' p) with hC'def
  have hPe : ∀ p ∈ S, P p = eul (B p) := fun p hp => eq_eul_invRoots (hP₀ p hp)
  have hQe : ∀ p ∈ S, Q p = eul (Cm p) := fun p hp => eq_eul_invRoots (hQ₀ p hp)
  have hP'e : ∀ p ∈ S, P' p = eul (B' p) := fun p hp => eq_eul_invRoots (hP'₀ p hp)
  have hQ'e : ∀ p ∈ S, Q' p = eul (C' p) := fun p hp => eq_eul_invRoots (hQ'₀ p hp)
  have hBs : ∀ p ∈ S, ∀ β ∈ B p, β ≠ 0 ∧ ‖β‖ ^ 2 < p :=
    fun p hp β hβ => invRoots_small (hP₀ p hp) (hP p hp) hβ
  have hB's : ∀ p ∈ S, ∀ β ∈ B' p, β ≠ 0 ∧ ‖β‖ ^ 2 < p :=
    fun p hp β hβ => invRoots_small (hP'₀ p hp) (hP' p hp) hβ

  have hCm0 : ∀ p ∈ S, ∀ β ∈ Cm p, β ≠ 0 := fun p hp β hβ => by
    obtain ⟨z, -, hz0, rfl⟩ := mem_invRoots (hQ₀ p hp) hβ
    exact inv_ne_zero hz0
  have hC'0 : ∀ p ∈ S, ∀ β ∈ C' p, β ≠ 0 := fun p hp β hβ => by
    obtain ⟨z, -, hz0, rfl⟩ := mem_invRoots (hQ'₀ p hp) hβ
    exact inv_ne_zero hz0

  set L : ℕ → ℂ[X] := fun p => Lpoly p (e p) (B' p) (Cm p) (C' p) with hLdef
  set R : ℕ → ℂ[X] := fun p => Rpoly p (e p) (B p) (B' p) (C' p) with hRdef
  set bigL : MvPolynomial S ℂ :=
    ∏ q ∈ S.attach, Polynomial.aeval (MvPolynomial.X q : MvPolynomial S ℂ) (L q) with hbigL
  set bigR : MvPolynomial S ℂ :=
    ∏ q ∈ S.attach, Polynomial.aeval (MvPolynomial.X q : MvPolynomial S ℂ) (R q) with hbigR

  have hfun : ∀ s' : ℝ, σ₀ ≤ s' → MvPolynomial.eval (xs S s') bigL =
      MvPolynomial.eval (xs S s') (MvPolynomial.C ω * bigR) := by
    intro s' hs'
    set s : ℂ := (s' : ℂ) with hsdef
    have hx : ∀ p ∈ S, ((p : ℂ) ^ (-s)) ≠ 0 := fun p hp => by
      rw [Ne, Complex.cpow_eq_zero_iff, not_and_or]
      exact Or.inl (by exact_mod_cast (hS p hp).ne_zero)

    have h1 := congrArg (fun z => (∏ p ∈ S, ((p : ℂ) ^ (-s)) ^ Dexp (e p) (B' p) (C' p)) * z)
      (hFE s' hs')
    have hL : (∏ p ∈ S, ((p : ℂ) ^ (-s)) ^ Dexp (e p) (B' p) (C' p)) *
        ((∏ p ∈ S, ((p : ℂ) ^ (-s)) ^ (e p)) *
          ∏ p ∈ S, (P' p).eval ((p : ℂ) ^ (s - 1)) * (Q p).eval ((p : ℂ) ^ (-s))) =
        ∏ p ∈ S, (L p).eval ((p : ℂ) ^ (-s)) := by
      rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun p hp => ?_
      rw [hLdef]
      simp only
      rw [← key_left p (e p) (B' p) (Cm p) (C' p) (hx p hp), ← cpow_sub_one_eq (hS p hp).ne_zero,
        hP'e p hp, hQe p hp, eval_eul, eval_eul]
      ring
    have hR : (∏ p ∈ S, ((p : ℂ) ^ (-s)) ^ Dexp (e p) (B' p) (C' p)) *
        (ω * ∏ p ∈ S, (P p).eval ((p : ℂ) ^ (-s)) * (Q' p).eval ((p : ℂ) ^ (s - 1))) =
        ω * ∏ p ∈ S, (R p).eval ((p : ℂ) ^ (-s)) := by
      rw [mul_left_comm, ← Finset.prod_mul_distrib]
      congr 1
      refine Finset.prod_congr rfl fun p hp => ?_
      rw [hRdef]
      simp only
      rw [← key_right p (e p) (B p) (B' p) (C' p) (hx p hp), ← cpow_sub_one_eq (hS p hp).ne_zero,
        hPe p hp, hQ'e p hp, eval_eul, eval_eul]
    rw [hL, hR] at h1
    rw [map_mul, MvPolynomial.eval_C, hbigL, hbigR, map_prod, map_prod]
    simp only [eval_aeval_X]
    unfold xs
    rw [Finset.prod_attach S (fun n : ℕ => (L n).eval (((n : ℕ) : ℂ) ^ (-s))),
      Finset.prod_attach S (fun n : ℕ => (R n).eval (((n : ℕ) : ℂ) ^ (-s)))]
    exact h1

  have hLR : bigL = MvPolynomial.C ω * bigR :=
    eq_of_eval_xs_eq hS ((Filter.eventually_ge_atTop σ₀).mono fun s hs => hfun s hs)

  have hLR0 : ∀ q ∈ S, L q * R q ≠ 0 := fun q _ =>
    mul_ne_zero (Lpoly_ne_zero _ _ _ _ _) (Rpoly_ne_zero _ _ _ _ _)
  obtain ⟨t, ht⟩ := exists_eval_ne_zero S (fun q => L q * R q) hLR0
  have htL : ∀ q ∈ S, (L q).eval t ≠ 0 := fun q hq h => ht q hq (by rw [eval_mul, h, zero_mul])
  have htR : ∀ q ∈ S, (R q).eval t ≠ 0 := fun q hq h => ht q hq (by rw [eval_mul, h, mul_zero])
  intro p hp
  have hp0 : p ≠ 0 := (hS p hp).ne_zero
  set i : S := ⟨p, hp⟩ with hidef
  have hspec := congrArg (spec i t) hLR
  rw [hbigL, hbigR, map_mul, spec_prod S.attach (Finset.mem_attach S i) t (fun q : S => L q),
    spec_prod S.attach (Finset.mem_attach S i) t (fun q : S => R q), MvPolynomial.algHom_C,
    Polynomial.algebraMap_eq] at hspec
  set κ₁ : ℂ := ∏ j ∈ S.attach.erase i, (L j).eval t with hκ₁
  set κ₂ : ℂ := ∏ j ∈ S.attach.erase i, (R j).eval t with hκ₂
  have hκ₁0 : κ₁ ≠ 0 := Finset.prod_ne_zero_iff.mpr fun j _ => htL j.1 j.2
  have hκ₂0 : κ₂ ≠ 0 := Finset.prod_ne_zero_iff.mpr fun j _ => htR j.1 j.2
  have hid : Polynomial.C κ₁ * Lpoly p (e p) (B' p) (Cm p) (C' p) =
      Polynomial.C (ω * κ₂) * Rpoly p (e p) (B p) (B' p) (C' p) := by
    have h' : L i * Polynomial.C κ₁ = Polynomial.C ω * (R i * Polynomial.C κ₂) := hspec
    rw [hLdef, hRdef] at h'
    simp only [hidef] at h'
    rw [Polynomial.C_mul]
    calc Polynomial.C κ₁ * Lpoly p (e p) (B' p) (Cm p) (C' p)
        = Lpoly p (e p) (B' p) (Cm p) (C' p) * Polynomial.C κ₁ := mul_comm _ _
      _ = Polynomial.C ω * (Rpoly p (e p) (B p) (B' p) (C' p) * Polynomial.C κ₂) := h'
      _ = _ := by ring

  have hCsmall : (∀ β ∈ Cm p, β ≠ 0 ∧ ‖β‖ ^ 2 < p) ∧ ∀ β ∈ C' p, β ≠ 0 ∧ ‖β‖ ^ 2 < p := by
    rcases hQ p hp with ⟨hQ1, hQ'1⟩ | ⟨hPu, hP'u, hQd, hQc, hQ'd, hQ'c⟩
    · exact ⟨fun β hβ => invRoots_small (hQ₀ p hp) hQ1 hβ,
        fun β hβ => invRoots_small (hQ'₀ p hp) hQ'1 hβ⟩
    · have hp2 : 2 ≤ p := (hS p hp).two_le
      have hBu : ∀ β ∈ B p, ‖β‖ = 1 := fun β hβ => norm_invRoots_eq_one (hP₀ p hp) hPu hβ
      have hB'u : ∀ β ∈ B' p, ‖β‖ = 1 := fun β hβ => norm_invRoots_eq_one (hP'₀ p hp) hP'u hβ
      rw [hQe p hp] at hQd hQc
      rw [hQ'e p hp] at hQ'd hQ'c
      obtain ⟨l, m, hlm, hlmn⟩ := exists_pair_of_norm_coeff_two (Cm p) (hCm0 p hp) hQd hQc
      obtain ⟨l', m', hlm', hlmn'⟩ := exists_pair_of_norm_coeff_two (C' p) (hC'0 p hp) hQ'd hQ'c

      have hroots := congrArg Polynomial.roots hid
      rw [roots_C_mul _ hκ₁0, roots_C_mul _ (mul_ne_zero hω hκ₂0),
        roots_Lpoly p (e p) (B' p) (Cm p) (C' p) (hCm0 p hp),
        roots_Rpoly p (e p) (B p) (B' p) (C' p) (fun β hβ => (hBs p hp β hβ).1)] at hroots
      obtain ⟨hCu, hC'u⟩ := norm_eq_one_of_roots_eq hp2 _ _ (B p) (B' p) (Cm p) (C' p) hBu hB'u
        hlm hlmn hlm' hlmn' hroots
      exact ⟨fun β hβ => small_of_norm_eq_one hp2 (hCu β hβ),
        fun β hβ => small_of_norm_eq_one hp2 (hC'u β hβ)⟩

  obtain ⟨he, hBC, hB'C'⟩ := one_prime hp0 (e p) (B p) (Cm p) (B' p) (C' p) (hBs p hp) hCsmall.1
    (hB's p hp) hCsmall.2 hκ₁0 (mul_ne_zero hω hκ₂0) hid
  refine ⟨he, ?_, ?_⟩
  · rw [hPe p hp, hQe p hp, hBC]
  · rw [hP'e p hp, hQ'e p hp, hB'C']

end S_DeligneSerre_eq_of_finite_eulerProduct_functionalEquation_of_norm_coeff_two_eq_one
end P2MW
export P2MW.S_DeligneSerre_eq_of_finite_eulerProduct_functionalEquation_of_norm_coeff_two_eq_one (solution)
