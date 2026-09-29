-- Prove2me | solution 2 for Diaz.candidate_indistinguishable
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-07T13:33:54.922373+00:00
-- url     : https://prove2.me/submissions/7f16a044-1afe-4bfc-9be2-7090c1fffcfb

import Mathlib
import Definitions.Def_Diaz_Closure
import Definitions.Def_Diaz_Instantiation

open ComplexConjugate
open Diaz

/-
Copyright (c) 2022 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/



/-!
# Evaluating symmetric polynomials

## Main declarations

* `pow_smul_sum_map_aroots_aeval_mem_range_algebraMap`: Given `k` a multiple of `p.leadingCoeff` and
  `e ≥ q.natDegree`, `k ^ e • ∑ i ∈ p.aroots A, q.aeval i` lies in the base ring.
* `MvPolynomial.symmetricSubalgebra.aevalMultiset` evaluates a symmetric polynomial at the elements
  of a multiset.
* `MvPolynomial.symmetricSubalgebra.sumPolynomial` maps `X` to `∑ i, X i`.

These are used in the proof of Lindemann-Weierstrass.
-/

@[expose] public section

open Finset
open scoped Polynomial

/-! ### Back-ports

Three lemmas used below that are not in this Mathlib revision. -/

@[simp] theorem Multiset.esymm_zero' {R : Type*} [CommSemiring R] (s : Multiset R) :
    s.esymm 0 = 1 := by
  simp [Multiset.esymm]

theorem Multiset.esymm_of_card_lt {R : Type*} [CommSemiring R] {s : Multiset R} {n : ℕ}
    (h : Multiset.card s < n) : s.esymm n = 0 := by
  rw [Multiset.esymm, Multiset.powersetCard_eq_empty n h]
  simp

theorem Polynomial.scaleRoots_aeval_smul' {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    (q : R[X]) (s : R) (x : A) :
    Polynomial.aeval (s • x) (q.scaleRoots s) = s ^ q.natDegree • Polynomial.aeval x q := by
  rw [Algebra.smul_def, Algebra.smul_def, Polynomial.aeval_def, Polynomial.aeval_def, map_pow]
  exact Polynomial.scaleRoots_eval₂_mul _ _ _

variable {σ τ R S A : Type*}

namespace MvPolynomial.symmetricSubalgebra

section CommSemiring

variable [Fintype σ] [Fintype τ] [CommRing R] [CommSemiring S] [Algebra R S]

variable (σ R) in
/-- `aevalMultiset` evaluates a symmetric polynomial at the elements of `s`. -/
noncomputable
def aevalMultiset (m : Multiset S) : symmetricSubalgebra σ R →ₐ[R] S :=
  (aeval (fun i : Fin (Fintype.card σ) ↦ m.esymm (i + 1))).comp
    (esymmAlgEquiv (σ := σ) R rfl).symm

theorem aevalMultiset_apply (m : Multiset S) (p : symmetricSubalgebra σ R) :
    aevalMultiset σ R m p =
      aeval (fun i : Fin _ ↦ m.esymm (i + 1)) ((esymmAlgEquiv σ R rfl).symm p) := rfl

theorem aevalMultiset_esymm (m : Multiset S) (i : Fin (Fintype.card σ)) :
    aevalMultiset σ R m ⟨esymm σ R (i + 1), esymm_isSymmetric σ R _⟩ = m.esymm (i + 1) := by
  simp [aevalMultiset_apply, esymmAlgEquiv_symm_apply]

theorem aevalMultiset_map (f : σ → S) (p : symmetricSubalgebra σ R) :
    aevalMultiset σ R (Finset.univ.val.map f) p = aeval f (p : MvPolynomial σ R) := by
  rw [aevalMultiset_apply]
  conv_rhs =>
    rw [← AlgEquiv.apply_symm_apply (esymmAlgEquiv σ R rfl) p]
  simp_rw [esymmAlgEquiv_apply, esymmAlgHom_apply, ← aeval_esymm_eq_multiset_esymm σ R,
    ← comp_aeval, AlgHom.coe_comp, Function.comp_apply]

theorem aevalMultiset_map_of_card_eq (f : τ → S) (p : symmetricSubalgebra σ R)
    (h : Fintype.card σ = Fintype.card τ) :
    aevalMultiset σ R (Finset.univ.val.map f) p =
      aeval (f ∘ Fintype.equivOfCardEq h) (p : MvPolynomial σ R) := by
  rw [← aevalMultiset_map (f ∘ Fintype.equivOfCardEq h) p,
    ← Multiset.map_map f (Fintype.equivOfCardEq h), Multiset.map_univ_val_equiv]

variable (σ) in
/-- `sumPolynomial σ p` is the map sending `X` to `∑ i, X i`. -/
noncomputable
def sumPolynomial (p : R[X]) : symmetricSubalgebra σ R :=
  ⟨∑ i, Polynomial.aeval (X i) p, fun e ↦ by
    simp_rw [map_sum, rename_eq_aeval, ← Polynomial.aeval_algHom_apply, aeval_X, (· ∘ ·)]
    rw [← Equiv.sum_comp e (fun i ↦ Polynomial.aeval (X i) p)]⟩

theorem coe_sumPolynomial (p : R[X]) :
    (sumPolynomial σ p : MvPolynomial σ R) = ∑ i, Polynomial.aeval (X i) p := rfl

theorem aevalMultiset_sumPolynomial
    {m : Multiset S} {p : R[X]} (hm : Multiset.card m = Fintype.card σ) :
    aevalMultiset σ R m (sumPolynomial σ p) = (m.map (fun x ↦ Polynomial.aeval x p)).sum := by
  classical
  conv_lhs => rw [← Multiset.map_univ_coe m]
  rw [aevalMultiset_map_of_card_eq _ _ (by simpa using hm.symm), coe_sumPolynomial, map_sum]
  simp_rw [← Polynomial.aeval_algHom_apply, aeval_X, (· ∘ ·)]
  rw [Equiv.sum_comp _ (fun x : m.ToType ↦ p.aeval x.fst), Finset.sum_eq_multiset_sum,
    ← Function.comp_def (p.aeval ·) (fun x : m.ToType ↦ x.fst), ← Multiset.map_map,
    Multiset.map_univ_coe]

theorem aevalMultiset_mem (B : Subalgebra R S)
    {m : Multiset S} {p : symmetricSubalgebra σ R}
    (h : ∀ i < Fintype.card σ, m.esymm (i + 1) ∈ B) :
    aevalMultiset σ R m p ∈ B := by
  rw [aevalMultiset_apply, MvPolynomial.aeval_def]
  exact MvPolynomial.eval₂_mem (fun _ _ ↦ B.algebraMap_mem _) fun i ↦ h _ i.2

end CommSemiring

section CommRing

variable [Fintype σ] [CommRing R] [CommRing S] [Algebra R S]
  [CommRing A] [Algebra S A] [Algebra R A] [IsScalarTower R S A]

theorem esymm_map_smul_aroots_mem_range_algebraMap [IsDomain A] {q : S[X]} {r : ℕ}
    (hsplit : (q.map (algebraMap S A)).Splits) :
    ((q.aroots A).map (q.leadingCoeff • ·)).esymm r ∈ Set.range (algebraMap S A) := by
  rw [← Algebra.mem_bot, ← Multiset.pow_smul_esymm]
  obtain rfl | hr0 := eq_or_ne r 0
  · simp
  obtain hr | hr := lt_or_ge q.natDegree r
  · simp [Multiset.esymm_of_card_lt ((Polynomial.card_roots_map_le_natDegree _).trans_lt hr)]
  obtain hlc | hlc := eq_or_ne (algebraMap S A q.leadingCoeff) 0
  · simp [Algebra.smul_def, map_pow, hlc, zero_pow hr0]
  have : q.leadingCoeff ^ r • (q.aroots A).esymm r =
      q.leadingCoeff ^ (r - 1) • ((-1) ^ r * (q.map (algebraMap S A)).coeff (q.natDegree - r)) := by
    have : (-1) ^ r * (q.map (algebraMap S A)).coeff (q.natDegree - r) =
        (q.map (algebraMap S A)).leadingCoeff * (q.aroots A).esymm r := by
      rw [Polynomial.coeff_eq_esymm_roots_of_card hsplit.natDegree_eq_card_roots.symm,
        Polynomial.natDegree_map_of_leadingCoeff_ne_zero _ hlc,
        Polynomial.leadingCoeff_map_of_leadingCoeff_ne_zero _ hlc,
        tsub_tsub_cancel_of_le hr,
        ← mul_assoc, mul_left_comm, ← mul_pow, ← pow_two, neg_one_sq, one_pow, mul_one]
      rw [Polynomial.natDegree_map_of_leadingCoeff_ne_zero _ hlc]
      exact Nat.sub_le _ _
    rw [this, Polynomial.leadingCoeff_map_of_leadingCoeff_ne_zero _ hlc,
      ← Algebra.smul_def, smul_smul, pow_sub_one_mul hr0]
  rw [this]
  exact SMulMemClass.smul_mem _ (mul_mem (pow_mem (by simp) _) (by simp))

theorem aevalMultiset_map_aroots_mem_range_algebraMap [IsDomain A]
    {q : S[X]} {p : symmetricSubalgebra σ R}
    (hsplit : (q.map (algebraMap S A)).Splits) :
    aevalMultiset σ R ((q.aroots A).map (q.leadingCoeff • ·)) p ∈ Set.range (algebraMap S A) :=
  aevalMultiset_mem (IsScalarTower.toAlgHom R S A).range
    fun _ _ ↦ esymm_map_smul_aroots_mem_range_algebraMap hsplit

end CommRing

end MvPolynomial.symmetricSubalgebra

namespace Polynomial

open MvPolynomial.symmetricSubalgebra

variable {R A : Type*} [CommRing R] [CommRing A] [IsDomain A] [Algebra R A] (p : R[X]) (q : R[X])

/-- `p.leadingCoeff ^ q.natDegree • ∑ i ∈ p.aroots A, q.aeval i` lies in the base ring. -/
theorem leadingCoeff_pow_natDegree_smul_sum_map_aroots_aeval_mem_range_algebraMap
    (hsplit : (p.map (algebraMap R A)).Splits) :
    p.leadingCoeff ^ q.natDegree • ((p.aroots A).map (q.aeval ·)).sum ∈
      Set.range (algebraMap R A) := by
  have : (fun x : A ↦ p.leadingCoeff ^ q.natDegree • q.aeval x) =
      ((q.scaleRoots p.leadingCoeff).aeval ·) ∘ (p.leadingCoeff • ·) :=
    _root_.funext fun x ↦ (scaleRoots_aeval_smul' _ _ _).symm
  rw [Multiset.smul_sum, Multiset.map_map, Function.comp_def, this,
    ← Multiset.map_map _ fun x => p.leadingCoeff • x]
  rw [← aevalMultiset_sumPolynomial (σ := Fin (p.aroots A).card) (by simp)]
  exact aevalMultiset_map_aroots_mem_range_algebraMap hsplit

/-- Given `k` a multiple of `p.leadingCoeff` and `e ≥ q.natDegree`,
`k ^ e • ∑ i ∈ p.aroots A, q.aeval i` lies in the base ring. -/
theorem pow_smul_sum_map_aroots_aeval_mem_range_algebraMap
    (k : R) (e : ℕ) (hk : p.leadingCoeff ∣ k) (he : q.natDegree ≤ e)
    (hsplit : (p.map (algebraMap R A)).Splits) :
    k ^ e • ((p.aroots A).map (q.aeval ·)).sum ∈ Set.range (algebraMap R A) := by
  obtain ⟨k, rfl⟩ := hk; obtain ⟨e, rfl⟩ := le_iff_exists_add.mp he
  have : (p.leadingCoeff * k) ^ (q.natDegree + e) =
      (p.leadingCoeff * k) ^ e * k ^ q.natDegree * p.leadingCoeff ^ q.natDegree := by
    ring
  rw [this, mul_smul, ← Algebra.mem_bot]
  apply SMulMemClass.smul_mem
  rw [Algebra.mem_bot]
  exact leadingCoeff_pow_natDegree_smul_sum_map_aroots_aeval_mem_range_algebraMap _ _ hsplit

end Polynomial
/-
Copyright (c) 2022 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/



/-!
# The Lindemann-Weierstrass theorem

## References

* [Jacobson, *Basic Algebra I, 4.12*][jacobson1974]
-/

noncomputable section

/-! ### Back-port of `Mathlib.Data.Finsupp.Quotient`, absent from this revision. -/

namespace Quot

variable {α β : Type*} {r : α → α → Prop} [Zero β] (f : α →₀ β) (h : ∀ a b, r a b → f a = f b)

/-- Lift a function `α →₀ β` to `Quot r →₀ β`. -/
protected def liftFinsupp : Quot r →₀ β := by
  classical
  refine ⟨Finset.image (mk r) f.support, Quot.lift f h, fun a => ⟨?_, ?_⟩⟩
  · rw [Finset.mem_image]; rintro ⟨b, hb, rfl⟩; exact Finsupp.mem_support_iff.mp hb
  · induction a using Quot.ind
    rw [lift_mk _ h]
    exact fun hb => Finset.mem_image_of_mem _ (Finsupp.mem_support_iff.mpr hb)

@[simp]
theorem liftFinsupp_mk (a : α) : Quot.liftFinsupp f h (Quot.mk r a) = f a :=
  rfl

end Quot

namespace Quotient

variable {α β : Type*} {s : Setoid α} [Zero β] (f : α →₀ β) (h : ∀ a b, s a b → f a = f b)

/-- Lift a function `α →₀ β` to `Quotient s →₀ β`. -/
protected def liftFinsupp : Quotient s →₀ β :=
  Quot.liftFinsupp f h

@[simp]
theorem liftFinsupp_mk (a : α) : Quotient.liftFinsupp f h ⟦a⟧ = f a :=
  rfl

end Quotient

namespace LindemannWeierstrass

open scoped AddMonoidAlgebra

open Finset

section mapDomainFixed

variable {F R K : Type*} [Field F] [CommSemiring R] [Algebra F R] [Field K] [Algebra F K]

variable (F R K) in
/-- The subalgebra of the `x : R[X]` fixed by `AddMonoidAlgebra.domCongrAut f` for all `f`. -/
def mapDomainFixed : Subalgebra R R[K] where
  carrier := {x | ∀ f : Gal(K/F), x.domCongr F R f = x}
  mul_mem' {a b} ha hb f := by rw [map_mul, ha, hb]
  add_mem' {a b} ha hb f := by rw [map_add, ha, hb]
  algebraMap_mem' r f := by simp

theorem mem_mapDomainFixed_iff {x : R[K]} :
    x ∈ mapDomainFixed F R K ↔ ∀ i j, i ∈ MulAction.orbit Gal(K/F) j → x.coeff i = x.coeff j := by
  simp? [MulAction.mem_orbit_iff, mapDomainFixed] says
    simp only [mapDomainFixed, MulAction.mem_orbit_iff, AlgEquiv.smul_def, forall_exists_index]
  refine ⟨fun h i j f hi => ?_, fun h f => ?_⟩
  · simp [← hi, ← congr($(h f).coeff (f j))]
  · ext i
    rw [AddMonoidAlgebra.coeff_domCongr]
    exact (h i (f.symm i) f (by simp)).symm

variable (F R K) in
/-- The equivalence between `mapDomainFixed F R K` and the `f : R[X]` with
`Setoid.ker f ≥ MulAction.orbitRel Gal(K/F) K`. -/
def mapDomainFixedEquivSubtype :
    mapDomainFixed F R K ≃ { f : R[K] // MulAction.orbitRel Gal(K/F) K ≤ Setoid.ker f.coeff } :=
  Equiv.subtypeEquivProp <| funext fun _ ↦ propext mem_mapDomainFixed_iff

namespace mapDomainFixed
variable [FiniteDimensional F K] [Normal F K]

open Classical in
/-- The element of `mapDomainFixed F R K` given by `a` on `x` and `0` elsewhere. -/
def single (x : ConjRootClass F K) (a : R) :
    mapDomainFixed F R K :=
  ⟨.ofCoeff <| Finsupp.indicator x.carrier.toFinset fun _ _ => a, by
    rw [mem_mapDomainFixed_iff]
    rintro i j h
    simp_rw [Finsupp.indicator_apply, Set.mem_toFinset, dite_eq_ite]
    congr 1
    simp_rw [ConjRootClass.mem_carrier, eq_iff_iff]
    apply Eq.congr_left
    rwa [ConjRootClass.mk_eq_mk, isConjRoot_iff_exists_algEquiv]⟩

theorem coeff_single_mul_single_zero_ne_zero_iff [CharZero F] [NoZeroDivisors R]
    (x : ConjRootClass F K) {a : R} (ha : a ≠ 0) (y : ConjRootClass F K) {b : R} (hb : b ≠ 0) :
    (mapDomainFixed.single x a * mapDomainFixed.single y b).val.coeff 0 ≠ 0 ↔ x = -y := by
  classical
  simp_rw [mapDomainFixed.single, MulMemClass.mk_mul_mk]
  have : IsAddTorsionFree R := .of_isTorsionFree F R
  simp_rw [Finsupp.indicator_eq_sum_single, AddMonoidAlgebra.ofCoeff_sum,
    sum_mul, mul_sum, AddMonoidAlgebra.ofCoeff_single, AddMonoidAlgebra.single_mul_single,
    AddMonoidAlgebra.coeff_sum, Finsupp.coe_finsetSum, Finset.sum_apply,
    AddMonoidAlgebra.coeff_single, Finsupp.single_apply, ← sum_product',
    sum_ite, sum_const_zero, add_zero, sum_const, smul_ne_zero_iff, mul_ne_zero_iff,
    iff_true_intro ha, iff_true_intro hb, and_true, Ne, card_eq_zero, filter_eq_empty_iff,
    not_forall, not_not, exists_prop', nonempty_prop, Prod.exists, mem_product, Set.mem_toFinset]
  convert ConjRootClass.exists_mem_carrier_add_eq_zero x y
  tauto

theorem coeff_single_mul_single_zero_eq_zero_iff [CharZero F] [NoZeroDivisors R]
    (x : ConjRootClass F K) {a : R} (ha : a ≠ 0) (y : ConjRootClass F K) {b : R} (hb : b ≠ 0) :
    (mapDomainFixed.single x a * mapDomainFixed.single y b).val.coeff 0 = 0 ↔ x ≠ -y :=
  (coeff_single_mul_single_zero_ne_zero_iff x ha y hb).not_right

/-- Auxiliary definition for `mapDomainFixed.toFinsupp`. -/
def toFinsuppAux : mapDomainFixed F R K ≃ (ConjRootClass F K →₀ R) := by
  classical
  refine (mapDomainFixedEquivSubtype F R K).trans
    { toFun f :=
        Quot.liftFinsupp (r := IsConjRoot _) f.val.coeff (by
          simp_rw [isConjRoot_iff_exists_algEquiv]
          exact f.2)
      invFun f := ⟨.ofCoeff ⟨f.support.biUnion fun i => i.carrier.toFinset,
        fun x => f (ConjRootClass.mk F x), fun i => ?_⟩, fun i j h ↦ ?_⟩
      left_inv _ := Subtype.ext <| AddMonoidAlgebra.ext <| Finsupp.ext fun x => rfl
      right_inv _ := Finsupp.ext fun x => Quot.inductionOn x fun i => rfl }
  · simp_rw [mem_biUnion, Set.mem_toFinset, ConjRootClass.mem_carrier, Finsupp.mem_support_iff,
      exists_eq_right']
  · rw [Setoid.ker_def, AddMonoidAlgebra.coeff_ofCoeff, Finsupp.coe_mk]
    exact congr_arg f (Quotient.sound (isConjRoot_iff_exists_algEquiv.mpr h))

@[simp]
private theorem toFinsuppAux_apply_apply_mk (f : mapDomainFixed F R K) (i : K) :
    toFinsuppAux f (ConjRootClass.mk F i) = f.val.coeff i :=
  rfl

/-- `mapDomainFixed F R K` is isomorphic to the finitely supported functions from
`ConjRootClass F K` into `R`. -/
def toFinsupp : mapDomainFixed F R K ≃ₗ[R] ConjRootClass F K →₀ R where
  toEquiv := toFinsuppAux
  map_add' x y := by
    ext i
    induction i
    simp_rw [Finsupp.coe_add, Pi.add_apply, Equiv.toFun_as_coe, toFinsuppAux_apply_apply_mk,
      AddMemClass.coe_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply]
  map_smul' r x := by
    ext i
    induction i
    simp_rw [Finsupp.coe_smul, Equiv.toFun_as_coe, toFinsuppAux_apply_apply_mk, SetLike.val_smul,
      RingHom.id_apply, AddMonoidAlgebra.coeff_smul, Pi.smul_apply, toFinsuppAux_apply_apply_mk,
      Finsupp.smul_apply]

@[simp]
theorem toFinsupp_apply_zero (f : mapDomainFixed F R K) :
    toFinsupp f 0 = f.val.coeff 0 :=
  rfl

theorem toFinsupp_apply_mk (f : mapDomainFixed F R K) (i : K) :
    toFinsupp f (ConjRootClass.mk F i) = f.val.coeff i :=
  rfl

theorem toFinsupp_single (x : ConjRootClass F K) (a : R) :
    toFinsupp (mapDomainFixed.single x a) = Finsupp.single x a := by
  classical
  ext i; induction i with | h i => ?_
  rw [toFinsupp_apply_mk]
  simp only [single]
  rw [Finsupp.single_apply, Finsupp.indicator_apply, dite_eq_ite]
  congr 1
  rw [Set.mem_toFinset, ConjRootClass.mem_carrier, eq_comm (a := x)]

theorem toFinsupp_sum_single (x : mapDomainFixed F R K) :
    (toFinsupp x).sum (mapDomainFixed.single (F := F) (K := K)) = x := by
  simp_rw [← toFinsupp.injective.eq_iff, map_finsuppSum, toFinsupp_single, Finsupp.sum_single]

open Classical in
theorem lift_eq_sum_toFinsupp (A : Type*) [Semiring A] [Algebra R A]
    (φ : Multiplicative K →* A) (x : mapDomainFixed F R K) :
    AddMonoidAlgebra.lift R A K φ x =
      (toFinsupp x).sum fun c xc ↦ xc • ∑ a ∈ c.carrier, φ (.ofAdd a) := by
  conv_lhs => rw [← mapDomainFixed.toFinsupp_sum_single x]
  have (s' : Finset K) (b : R) :
      ((Finsupp.indicator s' fun _ _ => b).sum fun a c => c • φ (.ofAdd a)) =
        ∑ a ∈ s', b • φ (.ofAdd a) :=
    Finsupp.sum_indicator_index _ fun i _ => by rw [zero_smul]
  conv_lhs => rw [Finsupp.sum, AddSubmonoidClass.coe_finsetSum]
  simp_rw [map_sum, AddMonoidAlgebra.lift_apply]
  change (∑ i ∈ (toFinsupp x).support, Finsupp.sum (AddMonoidAlgebra.coeff _) _) = _
  simp_rw [mapDomainFixed.single, this, smul_sum, Finsupp.sum]

end mapDomainFixed

end mapDomainFixed

open Complex

theorem descend_coeff (F : Type*) {K G S : Type*}
    [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [IsGalois F K]
    [AddCommMonoid G] [Semiring S] [NoZeroDivisors K[G]]
    (f : K[G] →+* S)
    (x : K[G]) (x0 : x ≠ 0) (hfx : f x = 0) :
    ∃ (y : F[G]), y ≠ 0 ∧ f (y.mapRingHom _ (algebraMap F K)) = 0 := by
  classical
  let y := ∏ f : Gal(K/F), x.mapAlgAut _ _ f
  have hy : ∀ f : Gal(K/F), y.mapAlgAut _ _ f = y := by
    intro f; dsimp only [y]
    simp_rw [map_prod, ← AlgEquiv.trans_apply, ← AlgEquiv.aut_mul, ← map_mul]
    exact (Group.mulLeft_bijective f).prod_comp fun g => x.mapAlgAut _ _ g
  have y0 : y ≠ 0 := by
    dsimp only [y]; rw [prod_ne_zero_iff]; intro f _hf
    rwa [map_ne_zero_iff]
    apply EquivLike.injective
  have hfy : f y = 0 := by
    suffices
      f (x.mapAlgAut _ _ 1 * ∏ f ∈ univ.erase 1, x.mapAlgAut _ _ f) = 0 by
      convert this
      exact (mul_prod_erase (univ : Finset Gal(K/F)) _ (mem_univ _)).symm
    simp [map_one, hfx]
  clear_value y
  have y_mem : ∀ i : G, y.coeff i ∈ Set.range (algebraMap F K) := by
    intro i
    rw [IsGalois.mem_range_algebraMap_iff_fixed]
    intro f
    simpa using congr($(hy f).coeff i)
  obtain ⟨y, rfl⟩ : y ∈ Set.range (AddMonoidAlgebra.mapRingHom _ (algebraMap F K)) := by
    rwa [AddMonoidAlgebra.coe_mapRingHom, AddMonoidAlgebra.range_map]
  refine ⟨y, (map_ne_zero_iff _ ?_).mp y0, hfy⟩
  simpa [AddMonoidAlgebra.coe_mapRingHom] using
    AddMonoidAlgebra.map_injective _ (algebraMap F K).injective

theorem exists_mapDomainFixed {F K S : Type*}
    [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
    [NoZeroDivisors F[K]] [Semiring S] [Algebra F S]
    (f : F[K] →ₐ[F] S)
    (x : F[K]) (x0 : x ≠ 0) (hfx : f x = 0) :
    ∃ (y : mapDomainFixed F F K), y ≠ 0 ∧ f y = 0 := by
  classical
  refine ⟨⟨∏ f : Gal(K/F), x.domCongr F _ (f : K ≃+ K), ?_⟩,
    fun h => absurd (Subtype.mk.inj h) ?_, ?_⟩
  · intro f
    rw [map_prod]
    simp_rw [← AlgEquiv.trans_apply, AddMonoidAlgebra.trans_domCongr_domCongr]
    exact (Group.mulLeft_bijective f).prod_comp fun g ↦ x.domCongrAut F _ (g : K ≃+ K)
  · simpa [prod_eq_zero_iff]
  · dsimp only
    rw [← mul_prod_erase univ _ (mem_univ .refl),
      show ((.refl : Gal(K/F)) : K ≃+ K) = .refl _ from rfl, AddMonoidAlgebra.domCongr_refl,
      AlgEquiv.coe_refl, id_def, map_mul, hfx, zero_mul]

open Classical in
theorem exists_conjRootClass_sum {F K S : Type*}
    [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [Normal F K] [CharZero F]
    [Semiring S] [Algebra F S]
    (φ : Multiplicative K →* S)
    (x : mapDomainFixed F F K) (x0 : x ≠ 0) (hx : AddMonoidAlgebra.lift F _ _ φ x = 0) :
    ∃ (w : F) (_w0 : w ≠ 0) (w' : ConjRootClass F K →₀ F) (_hw' : w' 0 = 0),
      (algebraMap F S w + w'.sum fun c wc ↦ wc • ∑ x ∈ c.carrier, φ (.ofAdd x)) = 0 := by
  rw [← (mapDomainFixed.toFinsupp.injective).ne_iff, map_zero] at x0
  obtain ⟨i, hi⟩ := Finsupp.support_nonempty_iff.mpr x0
  set x' := x * mapDomainFixed.single (-i) (1 : F) with x'_def
  have hx' : mapDomainFixed.toFinsupp x' 0 ≠ 0 := by
    rw [x'_def, ← mapDomainFixed.toFinsupp_sum_single x,
      Finsupp.sum, ← add_sum_erase _ _ hi, add_mul, sum_mul, map_add,
      Finsupp.add_apply, mapDomainFixed.toFinsupp_apply_zero, mapDomainFixed.toFinsupp_apply_zero]
    convert_to ((mapDomainFixed.single i (mapDomainFixed.toFinsupp x i) *
      mapDomainFixed.single (-i) 1).val.coeff 0 + 0 : F) ≠ 0
    · congr 1
      rw [AddSubmonoidClass.coe_finsetSum, AddMonoidAlgebra.coeff_sum,
        Finsupp.coe_finsetSum, Finset.sum_apply]
      refine sum_eq_zero fun j hj => ?_
      rw [mem_erase, Finsupp.mem_support_iff] at hj
      rw [mapDomainFixed.coeff_single_mul_single_zero_eq_zero_iff _ hj.2]
      · rw [neg_neg]; exact hj.1
      · exact one_ne_zero
    rw [add_zero, mapDomainFixed.coeff_single_mul_single_zero_ne_zero_iff]
    · rw [neg_neg]
    · rwa [Finsupp.mem_support_iff] at hi
    · exact one_ne_zero
  have zero_mem : (0 : ConjRootClass F K) ∈ (mapDomainFixed.toFinsupp x').support := by
    rwa [Finsupp.mem_support_iff]
  have lift_x' : AddMonoidAlgebra.lift F _ _ φ x' = 0 := by
    dsimp only [x']
    rw [Subalgebra.coe_mul, map_mul, hx, zero_mul]
  use mapDomainFixed.toFinsupp x' 0, hx', (mapDomainFixed.toFinsupp x').erase 0, Finsupp.erase_same
  rw [← lift_x', mapDomainFixed.lift_eq_sum_toFinsupp, ← Finsupp.add_sum_erase _ _ _ zero_mem]
  simp_rw [ConjRootClass.carrier_zero, Set.toFinset_singleton, sum_singleton, ofAdd_zero, map_one,
    Algebra.algebraMap_eq_smul_one]

variable {ι : Type*} [Fintype ι]

theorem exists_addMonoidAlgebra {K S : Type*}
    [Field K] [Semiring S] [Algebra K S]
    (φ : Multiplicative K →* S)
    (u' : ι → K) (u'_inj : Function.Injective u')
    (v' : ι → K) (v0 : v' ≠ 0)
    (h : ∑ i : ι, algebraMap K S (v' i) * φ (.ofAdd (u' i)) = 0) :
    ∃ (f : K[K]), f ≠ 0 ∧ AddMonoidAlgebra.lift _ _ _ φ f = 0 := by
  classical
  let f : K[K] := (AddMonoidAlgebra.ofCoeff <| Finsupp.equivFunOnFinite.symm v').mapDomain u'
  refine ⟨f, ?_, ?_⟩
  · simp_rw [Ne, funext_iff, Pi.zero_apply] at v0; push Not at v0
    obtain ⟨i, hv'i⟩ := v0
    have h : f.coeff (u' i) ≠ 0 := by
      unfold f
      rw [AddMonoidAlgebra.coeff_mapDomain, AddMonoidAlgebra.coeff_ofCoeff,
        Finsupp.mapDomain_apply u'_inj]
      simpa
    clear_value f
    rintro rfl
    simp at h
  · rw [AddMonoidAlgebra.lift_apply, ← h, AddMonoidAlgebra.coeff_mapDomain,
      Finsupp.sum_mapDomain_index_inj u'_inj]
    simp [Finsupp.sum_fintype, Algebra.smul_def]

theorem clear_coefficient_denominator (R : Type*) {F S ι : Type*}
    [CommRing R] [Nontrivial R] [Field F] [Algebra R F] [IsFractionRing R F]
    [Semiring S] [Algebra R S] [Algebra F S] [IsScalarTower R F S]
    (f : ι → S)
    (w : F) (w0 : w ≠ 0) (w' : ι →₀ F)
    (h : (algebraMap F S w + w'.sum fun c wc ↦ wc • f c) = 0) :
    ∃ (w : R) (_w0 : w ≠ 0) (w'' : ι →₀ R), w''.support ⊆ w'.support ∧
      (algebraMap R S w + w''.sum fun c wc ↦ wc • f c) = 0 := by
  classical
  obtain ⟨⟨N, N0⟩, hN⟩ :=
    IsLocalization.exist_integer_multiples_of_finset (nonZeroDivisors R) ({w} ∪ w'.frange)
  replace N0 := nonZeroDivisors.ne_zero N0
  simp only [mem_union, mem_singleton, IsLocalization.IsInteger, RingHom.mem_rangeS,
    forall_eq_or_imp] at hN
  choose x hx using hN.1
  choose x' hx' using hN.2
  set w'' := Finsupp.indicator w'.support
    (fun i hi ↦ x' (w' i) (by simpa [Finsupp.mem_frange] using hi)) with w''_def
  have hw'' : ∀ i, algebraMap R F (w'' i) = N • w' i := by
    simp only [w'', Finsupp.indicator_apply, Finsupp.mem_support_iff, ne_eq]
    intro i
    split_ifs with h0 <;> simp [h0, hx']
  have : IsCancelMulZero R := .of_faithfulSMul R F
  have x0 : x ≠ 0 := by
    rintro ⟨rfl⟩
    simp [eq_comm, N0, w0] at hx
  use x, x0, w'', Finsupp.support_indicator_subset _ _
  rw [Finsupp.sum] at h
  rw [Finsupp.sum_of_support_subset _ (Finsupp.support_indicator_subset _ _) _ (by simp), ← w''_def]
  simp_rw [Algebra.smul_def, IsScalarTower.algebraMap_apply R F S, hx, hw'', Algebra.smul_def,
    map_mul, mul_assoc, ← mul_sum, ← mul_add, ← Algebra.smul_def, h, smul_zero]

open Polynomial

open Classical in
theorem sum_conjRootClass_eq_sum_map_aroots {R F K S : Type*}
    [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [Normal F K] [CharZero F]
    [Field S] [Algebra K S] [Algebra F S] [IsScalarTower F K S]
    [CommSemiring R] [Algebra R S]
    (φ : Multiplicative S →* S) (w' : ConjRootClass F K →₀ R) (hw' : w' 0 = 0) :
    ∃ (w'' : F[X] →₀ R), (∀ p ∈ w''.support, p.eval 0 ≠ 0) ∧
      (w'.sum fun c wc ↦ wc • ∑ x ∈ c.carrier,
          φ.comp (algebraMap K S).toAddMonoidHom.toMultiplicative (.ofAdd x)) =
        w''.sum (fun p c ↦ c • ((p.aroots S).map fun x => φ (.ofAdd x)).sum) := by
  refine ⟨w'.mapDomain ConjRootClass.minpoly, ?_, ?_⟩
  · intro p hp
    classical
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp (Finsupp.mapDomain_support hp)
    suffices (c.minpoly.map (algebraMap F K)).eval (algebraMap F K 0) ≠ 0 by
      rwa [eval_map_algebraMap, aeval_algebraMap_apply, _root_.map_ne_zero] at this
    rw [RingHom.map_zero, ConjRootClass.minpoly.map_eq_prod, eval_prod, prod_ne_zero_iff]
    intro a ha
    rw [eval_sub, eval_X, eval_C, sub_ne_zero]
    rintro rfl
    rw [Set.mem_toFinset, ConjRootClass.mem_carrier, ConjRootClass.mk_zero] at ha
    subst ha
    simp [hw'] at hc
  · rw [Finsupp.sum_mapDomain_index (by simp) (by simp [add_smul])]
    refine sum_congr rfl fun c _hc => ?_
    dsimp
    rw [← c.splits_minpoly.map_aroots_algebraMap, c.aroots_minpoly_eq_carrier_val]
    simp

theorem clear_polynomial_denominator (R : Type*) {F S : Type*}
    [CommRing R] [Nontrivial R] [Field F] [Algebra R F] [IsFractionRing R F]
    [CommRing S] [IsDomain S] [Algebra R S] [Algebra F S] [IsScalarTower R F S]
    (f : S → S)
    (w : ℤ) (w' : F[X] →₀ ℤ) (hw' : ∀ p ∈ w'.support, p.eval 0 ≠ 0)
    (h : w + w'.sum (fun p c ↦ c • ((p.aroots S).map f).sum) = 0) :
    ∃ (w' : R[X] →₀ ℤ), (∀ p ∈ w'.support, p.eval 0 ≠ 0) ∧
      w + w'.sum (fun p c ↦ c • ((p.aroots S).map f).sum) = 0 := by
  choose b hb hbp using IsLocalization.integerNormalization_spec (nonZeroDivisors R) (S := F)
  refine ⟨w'.mapDomain (IsLocalization.integerNormalization (nonZeroDivisors R)), ?_, ?_⟩
  · intro p hp
    suffices aeval (algebraMap R F 0) p ≠ 0 by
      rwa [aeval_algebraMap_apply, map_ne_zero_iff _ (IsFractionRing.injective R F)] at this
    classical
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp (Finsupp.mapDomain_support hp)
    have : IsCancelMulZero R := .of_faithfulSMul R F
    rw [map_zero, ← eval_map_algebraMap, hbp, eval_smul, smul_ne_zero_iff]
    exact ⟨nonZeroDivisors.ne_zero (hb _), hw' q hq⟩
  · rw [← h, add_right_inj, Finsupp.sum_mapDomain_index (by simp) (by simp [add_mul])]
    congr!
    change roots _ = roots _
    rw [IsScalarTower.algebraMap_eq R F S, ← Polynomial.map_map, hbp,
      Algebra.smul_def, Polynomial.algebraMap_apply, Polynomial.map_mul, map_C, roots_C_mul]
    rw [map_ne_zero_iff _ (algebraMap F S).injective,
      map_ne_zero_iff _ (IsFractionRing.injective R F)]
    exact nonZeroDivisors.ne_zero (hb _)

theorem exists_sum_map_aroots {S : Type*}
    [Field S] [Algebra ℚ S] [IsAlgClosed S]
    (φ : Multiplicative S →* S)
    (u : ι → S) (hu : ∀ i, IsIntegral ℚ (u i))
    (u_inj : Function.Injective u) (v : ι → S) (hv : ∀ i, IsIntegral ℚ (v i)) (v0 : v ≠ 0)
    (h : ∑ i, v i * φ (.ofAdd <| u i) = 0) :
    ∃ (w : ℤ), w ≠ 0 ∧ ∃ (w' : ℤ[X] →₀ ℤ), (∀ p ∈ w'.support, p.eval 0 ≠ 0) ∧
      w + w'.sum (fun p c ↦ c • ((p.aroots S).map (φ <| .ofAdd ·)).sum) = 0 := by
  classical
  let s := univ.image u ∪ univ.image v
  have hs : ∀ x ∈ s, IsIntegral ℚ x := by simp [s, or_imp, forall_and, hu, hv]
  let poly : ℚ[X] := ∏ x ∈ s, minpoly ℚ x
  let K : IntermediateField ℚ S := IntermediateField.adjoin ℚ (poly.rootSet S)
  let _i : Algebra ℚ K := K.algebra'
  let _ : Algebra K S := K.val.toRingHom.toAlgebra
  have _ : IsSplittingField ℚ K poly :=
    IntermediateField.adjoin_rootSet_isSplittingField (IsAlgClosed.splits _)
  have : FiniteDimensional ℚ K := Polynomial.IsSplittingField.finiteDimensional K poly
  have : Normal ℚ K := .of_isSplittingField poly
  have : IsGalois ℚ K := ⟨⟩
  have algebraMap_K_apply x : algebraMap K S x = x := rfl
  have mem_K {x : S} (hx : x ∈ s) : x ∈ K := by
    apply IntermediateField.subset_adjoin
    rw [mem_rootSet, map_prod, prod_eq_zero_iff]
    exact ⟨prod_ne_zero_iff.mpr fun x hx => minpoly.ne_zero (hs x hx), x, hx, minpoly.aeval _ _⟩
  have u_mem (i) : u i ∈ K := mem_K (mem_union_left _ (mem_image_of_mem _ (mem_univ i)))
  have v_mem (i) : v i ∈ K := mem_K (mem_union_right _ (mem_image_of_mem _ (mem_univ i)))
  let u' : ι → K := fun i : ι => ⟨u i, u_mem i⟩
  let v' : ι → K := fun i : ι => ⟨v i, v_mem i⟩
  obtain ⟨f, f0, hf⟩ : ∃ (f : K[K]), f ≠ 0 ∧
    AddMonoidAlgebra.lift _ _ _
      (φ.comp (algebraMap K S).toAddMonoidHom.toMultiplicative) f = 0 := by
    refine exists_addMonoidAlgebra _ u' ?_ v' ?_ ?_
    · exact fun i j hij ↦ u_inj (Subtype.mk.inj hij)
    · simp_rw [Ne, funext_iff, Pi.zero_apply] at v0 ⊢; push Not at v0 ⊢
      exact v0.imp fun i hvi ↦ by rwa [Ne, ← ZeroMemClass.coe_eq_zero]
    · simpa [algebraMap_K_apply, u', v']
  obtain ⟨f, f0, hf⟩ := descend_coeff ℚ _ f f0 hf
  rw [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AddMonoidAlgebra.lift_mapRingHom_algebraMap] at hf
  obtain ⟨f, f0, hf⟩ := exists_mapDomainFixed _ f f0 hf
  obtain ⟨w, w0, w', hw', h⟩ := exists_conjRootClass_sum _ f f0 hf
  obtain ⟨w', hw', h'⟩ := sum_conjRootClass_eq_sum_map_aroots φ w' hw'
  obtain ⟨w, w0, w', hw'', h⟩ := clear_coefficient_denominator ℤ _ w w0 w' (h' ▸ h)
  exact ⟨w, w0, clear_polynomial_denominator ℤ _ w w' (fun p hp ↦ hw' p (hw'' hp)) h⟩

end LindemannWeierstrass
/-
Copyright (c) 2022 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/



/-!
# The Lindemann-Weierstrass theorem

## References

* [Jacobson, *Basic Algebra I, 4.12*][jacobson1974]
-/

@[expose] public section

open scoped Nat

open Complex Finset Polynomial

variable {ι : Type*}

theorem linearIndependent_exp' [Fintype ι] (u : ι → ℂ) (hu : ∀ i, IsIntegral ℚ (u i))
    (u_inj : Function.Injective u) (v : ι → ℂ) (hv : ∀ i, IsIntegral ℚ (v i))
    (h : ∑ i, v i * exp (u i) = 0) : v = 0 := by
  -- Start of proof of theorem 4.22 (Jacobson, p. 281).
  -- Assume v is not identically zero.
  by_contra! v0
  -- This implies we have a similar sum `w + ∑ p, w' p • ∑ u ∈ p.aroots ℂ, exp u = 0` where
  -- `w` and `w' p` are integers, `w ≠ 0`, and the `p` in the support of `w'` are integral
  -- polynomials with nonzero constant coefficients.
  obtain ⟨w, w0, w'', p0, h⟩ :=
    LindemannWeierstrass.exists_sum_map_aroots expMonoidHom u hu u_inj v hv v0 h
  simp_rw [expMonoidHom_apply, toAdd_ofAdd] at h
  let p : w''.support → ℤ[X] := Subtype.val
  let w' := w'' ∘ p
  -- Note that none of the `p j` are zero.
  have p0' : ∀ j, p j ≠ 0 := by intro ⟨_, hp⟩ rfl; simpa using p0 _ hp
  -- And the sum is not trivial. (Otherwise `w = 0`.)
  have I : Nonempty w''.support := by
    rw [Finset.nonempty_coe_sort, Finsupp.support_nonempty_iff]
    rintro rfl; rw [Finsupp.sum_zero_index, add_zero, Int.cast_eq_zero] at h
    exact w0 h
  -- Let `P` be the product of the `p j`, which has a nonzero constant coefficient as well.
  let P := ∏ j, p j
  have P0 : P.eval 0 ≠ 0 := by
    dsimp only [P]; rw [eval_prod, prod_ne_zero_iff]; exact fun ⟨p, hp⟩ _ => p0 p hp
  have P0' : P ≠ 0 := by intro h; simp [h] at P0
  have mem_aroots {j x} (hx : x ∈ (p j).aroots ℂ) : x ∈ P.aroots ℂ := by
    rw [mem_aroots', Polynomial.map_ne_zero_iff (algebraMap ℤ ℂ).injective_int] at hx ⊢
    rw [map_prod]
    exact ⟨P0', prod_eq_zero (mem_univ _) hx.2⟩
  -- Now let `K` be the splitting field of `P` in ℂ.
  obtain ⟨K, _, _, _, _, _⟩ : ∃ (K : Type) (_ : Field K) (_ : Algebra ℚ K) (_ : Algebra K ℂ)
      (_ : IsScalarTower ℚ K ℂ), IsSplittingField ℚ K (P.map (algebraMap ℤ ℚ)) :=
    ⟨IntermediateField.adjoin ℚ ((P.map (algebraMap ℤ ℚ)).rootSet ℂ),
      inferInstance, inferInstance, inferInstance, inferInstance,
      IntermediateField.adjoin_rootSet_isSplittingField (IsAlgClosed.splits _)⟩
  have : CharZero K := algebraRat.charZero K
  -- All the `p j` split in `K`.
  have splits_p (j) : ((p j).map (algebraMap ℤ K)).Splits := by
    have P0'' : P.map (algebraMap ℤ K) ≠ 0 := by
      rwa [Polynomial.map_ne_zero_iff (algebraMap ℤ K).injective_int]
    refine .of_dvd ?_ P0'' ?_
    · rw [IsScalarTower.algebraMap_eq ℤ ℚ K, ← Polynomial.map_map]
      exact IsSplittingField.splits _ _
    simp_rw [P, Polynomial.map_prod]
    exact dvd_prod_of_mem _ (mem_univ _)
  -- The roots of `p j` in `ℂ` are simply the roots in `K` embedded into `ℂ`
  have aroots_K_eq_aroots_ℂ (j) (f : ℂ → ℂ) :
      (((p j).aroots K).map fun x => f (algebraMap K ℂ x)) = (((p j).aroots ℂ).map f) := by
    rw [← (splits_p j).map_aroots_algebraMap (B := ℂ), Multiset.map_map, Function.comp_def]
  replace h : ↑w + ∑ j, w' j • (((p j).aroots ℂ).map exp).sum = 0 := by
    rwa [Finsupp.sum, ← Finset.sum_coe_sort] at h
  simp_rw [← aroots_K_eq_aroots_ℂ] at h
  -- The following roughly matches Jacobson, p. 286.
  -- Let `k` be the product of the leading coefficients of the `p j` (i.e., `P.leadingCoeff`).
  let k : ℤ := ∏ j, (p j).leadingCoeff
  have k0 : k ≠ 0 := prod_ne_zero_iff.mpr fun j _hj => leadingCoeff_ne_zero.mpr (p0' j)
  have sz_h (j) : (p j).leadingCoeff ∣ k := dvd_prod_of_mem _ (mem_univ _)
  -- Now there exists a constant `c : ℝ`, such that for each prime `p > |P₀|` we have `nₚ : ℤ` and
  -- `gₚ : ℤ[X]` such that
  -- * `p` does not divide `nₚ`
  -- * `deg(gₚ) ≤ p * deg(f) - 1` (`≤ p * deg(f)` is sufficient)
  -- * all complex roots `r` of `P` satisfy `|nₚ * exp r - p * gₚ(r)| ≤ c ^ p / (p - 1)!`
  obtain ⟨c, hc'⟩ := LindemannWeierstrass.exp_polynomial_approx P P0
  -- Let `L` be a nonnegative upper bound on the norms of the coefficients of the sum.
  let L := sup' univ univ_nonempty fun j => ‖w' j‖
  have L0 : 0 ≤ L := I.elim fun j => (norm_nonneg (w' j)).trans (le_sup' (‖w' ·‖) (mem_univ j))
  -- Now there exists a sufficiently large prime `q` such that
  -- `L * (∑ i, ((p i).aroots ℂ).card) * (‖k‖ ^ P.natDegree * c) ^ q / (q - 1)! < 1`.
  let N := max (P.eval 0).natAbs (max k.natAbs w.natAbs)
  obtain ⟨q, hqN, prime_q, hq⟩ : ∃ q : ℕ, N < q ∧ Nat.Prime q ∧
      L * (∑ i, ((p i).aroots ℂ).card) * (‖k‖ ^ P.natDegree * c) ^ q / (q - 1)! < 1 := by
    have (x : ℝ) : Filter.Tendsto (fun n ↦ x ^ n / (n - 1)!) .atTop (nhds 0) := by
      suffices Filter.Tendsto ((fun n ↦ x ^ (n + 1) / n !) ∘ (· - 1)) .atTop (nhds 0) from
        this.congr' <| Filter.eventually_atTop.mpr ⟨1, fun _ h ↦ by simp [h]⟩
      have := (FloorSemiring.tendsto_pow_div_factorial_atTop x).const_mul x
      simp_rw [← mul_div_assoc, ← pow_succ', mul_zero] at this
      exact this.comp (Filter.tendsto_atTop_atTop.mpr fun b ↦ ⟨b + 1, fun _ ↦ by omega⟩)
    simpa only [Nat.succ_le_iff, mul_div_assoc] using
      Filter.Frequently.forall_exists_of_atTop
        ((Filter.frequently_atTop.mpr Nat.exists_infinite_primes).and_eventually <|
          Filter.Tendsto.eventually_lt_const (u := 1) (by simp)
            ((this (‖k‖ ^ P.natDegree * c)).const_mul (L * ∑ i, Multiset.card ((p i).aroots ℂ))))
        (N + 1)
  -- And this `q` is in particular large enough to apply `hc'`.
  obtain ⟨n, hn, gp, hgp, hc⟩ := hc' q (by order) prime_q
  replace hgp : gp.natDegree ≤ P.natDegree * q := by rw [mul_comm]; exact hgp.trans tsub_le_self
  clear hc'
  let t := P.natDegree * q
  -- Now `k` is a positive integer such that for every `j`,
  -- `k ^ t * ∑ u ∈ (p j).aroots K, gp u` is an integer.
  -- Let `sz` be the vector such that `sz j` is that corresponding integer.
  choose sz hsz using fun j ↦
    pow_smul_sum_map_aroots_aeval_mem_range_algebraMap (p j) gp k t (sz_h j) hgp (splits_p j)
  replace hsz : k ^ t • ∑ j, w' j • (((p j).aroots K).map fun x => gp.aeval x).sum =
      algebraMap ℤ K (∑ j, w' j • sz j) := by
    simp_rw [smul_sum, smul_comm (k ^ t), ← hsz, map_sum, map_zsmul]
  -- Then `k ^ t * n * w + q * ∑ j, w' j • sz j
  --  = k ^ t • (∑ j, w' j • ∑ u ∈ (p j).aroots K, q • gp u - n • exp u))`.
  have H' := calc
    ((k ^ t * n * w + q * ∑ j, w' j • sz j : ℤ) : ℂ)
    _ = algebraMap K ℂ (k ^ t • n • (w : K) + q • algebraMap ℤ K (∑ j, w' j • sz j)) := by
      simp [mul_assoc]
    _ = algebraMap K ℂ
          (k ^ t • n • (w : K) +
            q • k ^ t • ∑ j, w' j • (((p j).aroots K).map fun x => gp.aeval x).sum) := by
      rw [hsz]
    _ = algebraMap K ℂ
          (k ^ t • (n • (w : K) +
            q • ∑ j, w' j • (((p j).aroots K).map fun x => gp.aeval x).sum)) := by
      simp_rw [smul_add, smul_comm (k ^ t)]
    _ = k ^ t • (n • (w : ℂ) +
          q • ∑ j, w' j • (((p j).aroots K).map fun x => gp.aeval (algebraMap K ℂ x)).sum) := by
      simp only [map_add, map_nsmul, map_zsmul, map_intCast, map_sum, map_multiset_sum,
        Multiset.map_map, Function.comp, ← aeval_algebraMap_apply]
    _ = k ^ t •
        (q • ∑ j, w' j • (((p j).aroots K).map fun x => gp.aeval (algebraMap K ℂ x)).sum -
          n • ∑ j, w' j • (((p j).aroots K).map fun x => exp (algebraMap K ℂ x)).sum) := by
      rw [← eq_neg_iff_add_eq_zero] at h
      rw [h, smul_neg, neg_add_eq_sub]
    _ = k ^ t •
          (∑ j, w' j • (((p j).aroots K).map fun x => q • gp.aeval (algebraMap K ℂ x)).sum -
            ∑ j, w' j • (((p j).aroots K).map fun x => n • exp (algebraMap K ℂ x)).sum) := by
      simp_rw [smul_sum, Multiset.smul_sum, Multiset.map_map, Function.comp,
        smul_comm n, smul_comm q]
    _ = k ^ t • ∑ j, w' j • (((p j).aroots K).map fun x =>
                        q • gp.aeval (algebraMap K ℂ x) - n • exp (algebraMap K ℂ x)).sum := by
      simp only [← smul_sub, ← sum_sub_distrib, ← Multiset.sum_map_sub]
    _ = k ^ t • ∑ j, w' j • (((p j).aroots ℂ).map fun x => q • gp.aeval x - n • exp x).sum := by
      congr!
      exact aroots_K_eq_aroots_ℂ _ (fun x ↦ q • gp.aeval x - n • exp x)
  -- And, as we've taken `q` sufficiently large, `‖k ^ t * n * w + q * ∑ j, w' j • sz j‖ < 1`.
  have H := calc
    ‖((k ^ t * n * w + q * ∑ j, w' j • sz j : ℤ) : ℂ)‖
    _ = ‖k ^ t • ∑ j, w' j • (((p j).aroots ℂ).map fun x => q • gp.aeval x - n • exp x).sum‖ := by
      rw [H']
    _ = ‖k ^ t‖ * ‖∑ j, w' j • (((p j).aroots ℂ).map fun x => q • gp.aeval x - n • exp x).sum‖ := by
      rw [norm_smul]
    _ ≤ ‖k ^ t‖ * ∑ j, L * ‖(((p j).aroots ℂ).map fun x => q • gp.aeval x - n • exp x).sum‖ := by
      grw [norm_sum_le]
      simp_rw [norm_smul]
      gcongr
      exact le_sup' (‖w' ·‖) (mem_univ _)
    _ ≤ ‖k ^ t‖ *
        ∑ j, L * (Multiset.map (fun x ↦ ‖q • (aeval x) gp - n • cexp x‖) ((p j).aroots ℂ)).sum := by
      gcongr
      grw [norm_multiset_sum_le]
      rw [Multiset.map_map, Function.comp_def]
    _ ≤ ‖k ^ t‖ * ∑ j, L * (((p j).aroots ℂ).map fun _ => c ^ q / ↑(q - 1)!).sum := by
      gcongr
      refine Multiset.sum_map_le_sum_map _ _ fun x hx => ?_
      rw [norm_sub_rev]
      exact hc (mem_aroots hx)
    _ = L * (∑ i, ((p i).aroots ℂ).card) * (‖k‖ ^ P.natDegree * c) ^ q / (q - 1)! := by
      simp_rw [norm_pow, Multiset.map_const', Multiset.sum_replicate, ← mul_sum, ← sum_smul,
        nsmul_eq_mul]
      ring
    _ < 1 := hq
  -- The left-hand side is an integer with norm less than one, so is zero. Since the second term
  -- is a multiple of `q`, so is the first term.
  rw [norm_intCast, ← Int.cast_abs, ← Int.cast_one, Int.cast_lt, Int.abs_lt_one_iff] at H
  replace H : q ∣ (k ^ t * n * w).natAbs := by
    rw [← Int.ofNat_dvd_left, ← Int.dvd_add_self_mul, H]
    exact dvd_zero _
  -- But `q` is prime and divides none of the factors, so we have our contradiction.
  simp_rw [Int.natAbs_mul, prime_q.dvd_mul, Int.natAbs_pow] at H
  obtain (H | H) | H := H
  · order [Nat.le_of_dvd (Int.natAbs_pos.mpr k0) <| prime_q.dvd_of_dvd_pow H]
  · rw [← Int.ofNat_dvd_left] at H
    contradiction
  · order [Nat.le_of_dvd (Int.natAbs_pos.mpr w0) H]

theorem linearIndependent_exp (u : ι → integralClosure ℚ ℂ) (u_inj : u.Injective) :
    LinearIndependent (integralClosure ℚ ℂ) fun i ↦ exp (u i) :=
  linearIndependent_iff'.mpr fun s v h ↦ by
    simpa [funext_iff] using linearIndependent_exp' (ι := s) (u ·) (u · |>.2)
      (fun i j ↦ by simpa [Subtype.coe_inj] using @u_inj i j)
      (v ·) (v · |>.2) (by simpa [sum_attach _ fun x ↦ v x * cexp (u x)])

theorem algebraicIndependent_exp (u : ι → integralClosure ℚ ℂ) (hu : LinearIndependent ℕ u) :
    AlgebraicIndependent (integralClosure ℚ ℂ) fun i ↦ exp (u i) := by
  rw [algebraicIndependent_iff]
  intro p hp
  simp_rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_eq, ← Algebra.smul_def, ← exp_nsmul,
    ← exp_sum] at hp
  norm_cast at hp
  apply AddMonoidAlgebra.ext
  apply linearIndependent_iff.mp (linearIndependent_exp (fun e ↦ ∑ i ∈ e.support, e i • u i) _)
  exacts [hp, hu]

theorem transcendental_exp {a : ℂ} (a0 : a ≠ 0) (ha : IsAlgebraic ℤ a) :
    Transcendental ℤ (exp a) := by
  intro h
  have is_integral_a : IsIntegral ℚ a :=
    isAlgebraic_iff_isIntegral.mp (ha.extendScalars (algebraMap ℤ ℚ).injective_int)
  have is_integral_expa : IsIntegral ℚ (exp a) :=
    isAlgebraic_iff_isIntegral.mp (h.extendScalars (algebraMap ℤ ℚ).injective_int)
  refine by
    simpa [Fin.forall_fin_succ] using linearIndependent_exp' ![a, 0] ?_ ?_ ![1, -exp a] ?_ ?_
  · intro i; fin_cases i
    exacts [is_integral_a, isIntegral_zero]
  · intro i j; fin_cases i, j <;> simp [a0.symm, *]
  · intro i; fin_cases i; exacts [isIntegral_one, is_integral_expa.neg]
  · simp

theorem transcendental_e : Transcendental ℤ (exp 1) :=
  transcendental_exp one_ne_zero isAlgebraic_one

theorem transcendental_log {u : ℂ} (hu0 : Complex.log u ≠ 0) (hu : IsAlgebraic ℤ u) :
    Transcendental ℤ (Complex.log u) := by
  intro h
  have := transcendental_exp hu0 h
  rw [Complex.exp_log (by aesop)] at this
  contradiction

/-! ## The closure theorem, end to end -/

open scoped Cardinal

namespace Diaz

/-- **Hermite–Lindemann, contrapositive form.** -/
theorem transcendental_of_candidate' {u : ℂ} (hu : u ≠ 0)
    (hexp : IsAlgebraic ℚ (Complex.exp u)) : Transcendental ℚ u := by
  intro hualg
  have h1 : IsIntegral ℚ u := isAlgebraic_iff_isIntegral.mp hualg
  have h2 : IsIntegral ℚ (Complex.exp u) := isAlgebraic_iff_isIntegral.mp hexp
  refine by
    simpa [Fin.forall_fin_succ] using
      linearIndependent_exp' ![u, 0] ?_ ?_ ![1, -Complex.exp u] ?_ ?_
  · intro i; fin_cases i
    exacts [h1, isIntegral_zero]
  · intro i j; fin_cases i, j <;> simp [hu.symm, *]
  · intro i; fin_cases i; exacts [isIntegral_one, h2.neg]
  · simp

/-- A candidate is transcendental over any base algebraic over `ℚ`. -/
theorem transcendental_candidate_over_base' {L : Subfield ℂ}
    [Algebra.IsAlgebraic ℚ (↥L)] {u : ℂ} (hu : u ≠ 0)
    (hexp : IsAlgebraic ℚ (Complex.exp u)) : Transcendental (↥L) u :=
  fun hcon => transcendental_of_candidate' hu hexp (hcon.restrictScalars ℚ)

/-- A transcendental element is non-zero. -/
theorem transcendental_ne_zero' {F : Type*} [Field F] [Algebra F ℂ] {z : ℂ}
    (h : Transcendental F z) : z ≠ 0 := by
  rintro rfl
  exact h isAlgebraic_zero

/-- `Q̄` is stable under complex conjugation. -/
theorem conj_mem_Qbar' {z : ℂ} (h : z ∈ Qbar) : conj z ∈ Qbar := by
  rw [Qbar] at h ⊢
  have h1 : IsAlgebraic ℚ z := IsIntegral.isAlgebraic h
  have h2 : IsAlgebraic ℚ (conj z) :=
    h1.algHom (((starRingEnd ℂ) : ℂ →+* ℂ).toRatAlgHom)
  exact h2.isIntegral

/-- **Steinitz extension.** Two elements transcendental over a subfield `K ⊆ ℂ` are
interchanged by a ring endomorphism of `ℂ` fixing `K` pointwise. -/
theorem exists_ringHom_of_transcendental' {K : Subfield ℂ} {u t : ℂ}
    (hu : Transcendental (↥K) u) (ht : Transcendental (↥K) t) :
    ∃ Φ : ℂ →+* ℂ, (∀ a ∈ K, Φ a = a) ∧ Φ u = t := by
  have hu' : AlgebraicIndepOn (↥K) id ({u} : Set ℂ) := by
    exact (algebraicIndependent_singleton_iff (R := ↥K)
      (x := fun x : ({u} : Set ℂ) => id (x : ℂ)) ⟨u, rfl⟩).2 hu
  have ht' : AlgebraicIndepOn (↥K) id ({t} : Set ℂ) := by
    exact (algebraicIndependent_singleton_iff (R := ↥K)
      (x := fun x : ({t} : Set ℂ) => id (x : ℂ)) ⟨t, rfl⟩).2 ht
  obtain ⟨B, huB, hB⟩ := exists_isTranscendenceBasis_superset hu'
  obtain ⟨C, htC, hC⟩ := exists_isTranscendenceBasis_superset ht'
  have hcard : #(↥B) = #(↥C) := hB.cardinalMk_eq hC
  obtain ⟨f⟩ := Cardinal.eq.mp hcard
  set iu : ↥B := ⟨u, huB rfl⟩ with hiu
  set it : ↥C := ⟨t, htC rfl⟩ with hit
  set e : ↥B ≃ ↥C := f.trans (Equiv.swap (f iu) it) with he
  have hei : e iu = it := by simp [he]
  set v : ↥B → ℂ := ((↑) : ↥B → ℂ) with hvdef
  set w : ↥C → ℂ := ((↑) : ↥C → ℂ) with hwdef
  have i1 : IsAlgClosure (Algebra.adjoin (↥K) (Set.range v)) ℂ :=
    IsAlgClosed.isAlgClosure_of_transcendence_basis v hB
  have i2 : IsAlgClosure (Algebra.adjoin (↥K) (Set.range w)) ℂ :=
    IsAlgClosed.isAlgClosure_of_transcendence_basis w hC
  set ε : Algebra.adjoin (↥K) (Set.range v) ≃ₐ[↥K] Algebra.adjoin (↥K) (Set.range w) :=
    hB.1.aevalEquiv.symm.trans ((MvPolynomial.renameEquiv (↥K) e).trans hC.1.aevalEquiv) with hε
  set Phi : ℂ ≃+* ℂ := IsAlgClosure.equivOfEquiv ℂ ℂ ε.toRingEquiv with hPhi
  refine ⟨Phi.toRingHom, ?_, ?_⟩
  · intro a ha
    have h1 : (a : ℂ) = algebraMap (Algebra.adjoin (↥K) (Set.range v)) ℂ
        (algebraMap (↥K) (Algebra.adjoin (↥K) (Set.range v)) ⟨a, ha⟩) := by
      rw [← IsScalarTower.algebraMap_apply]
      rfl
    rw [RingEquiv.toRingHom_eq_coe, RingHom.coe_coe]
    conv_lhs => rw [h1]
    rw [hPhi, IsAlgClosure.equivOfEquiv_algebraMap]
    show algebraMap (Algebra.adjoin (↥K) (Set.range w)) ℂ
      (ε (algebraMap (↥K) (Algebra.adjoin (↥K) (Set.range v)) ⟨a, ha⟩)) = a
    rw [AlgEquiv.commutes, ← IsScalarTower.algebraMap_apply]
    rfl
  · have h2 : u = algebraMap (Algebra.adjoin (↥K) (Set.range v)) ℂ
        (hB.1.aevalEquiv (MvPolynomial.X iu)) := by
      rw [AlgebraicIndependent.algebraMap_aevalEquiv]
      simp [hvdef, hiu]
    rw [RingEquiv.toRingHom_eq_coe, RingHom.coe_coe]
    conv_lhs => rw [h2]
    rw [hPhi, IsAlgClosure.equivOfEquiv_algebraMap]
    show algebraMap (Algebra.adjoin (↥K) (Set.range w)) ℂ
      (ε (hB.1.aevalEquiv (MvPolynomial.X iu))) = t
    rw [hε]
    simp only [AlgEquiv.trans_apply, AlgEquiv.symm_apply_apply,
      MvPolynomial.renameEquiv_apply, MvPolynomial.rename_X, hei]
    rw [AlgebraicIndependent.algebraMap_aevalEquiv]
    simp [hwdef, hit]

/-- `u` lies in its own hull. -/
theorem self_mem_hull' {K : Subfield ℂ} {u : ℂ} : u ∈ hull K u :=
  Subfield.subset_closure (Or.inr rfl)

/-- With `ρ = u * conj u`, the conjugate of `u` is `ρ / u`. -/
theorem conj_eq_rho_div' {u : ℂ} (hu : u ≠ 0) : (u * conj u) / u = conj u := by
  field_simp

/-- Two ring homomorphisms of `ℂ` agreeing on `K` and at `u` agree on the whole hull. -/
theorem eqOn_hull' {K : Subfield ℂ} {u : ℂ} (f g : ℂ →+* ℂ)
    (hK : ∀ z ∈ K, f z = g z) (hu : f u = g u) :
    ∀ z ∈ hull K u, f z = g z := by
  intro z hz
  induction hz using Subfield.closure_induction with
  | mem x hx =>
      rcases hx with hx | hx
      · exact hK x hx
      · rw [Set.mem_singleton_iff] at hx; subst hx; exact hu
  | one => simp
  | add x y _ _ hx hy => rw [map_add, map_add, hx, hy]
  | neg x _ hx => rw [map_neg, map_neg, hx]
  | inv x _ hx => rw [map_inv₀, map_inv₀, hx]
  | mul x y _ _ hx hy => rw [map_mul, map_mul, hx, hy]

/-- **An isomorphism matching the generators intertwines conjugation.** -/
theorem conj_comm' {K : Subfield ℂ} {u t : ℂ} (Φ : ℂ →+* ℂ) (hK : ∀ a ∈ K, Φ a = a)
    (hKconj : ∀ a ∈ K, conj a ∈ K)
    (hu0 : u ≠ 0) (ht0 : t ≠ 0) (hΦu : Φ u = t)
    (hρ : u * conj u ∈ K) (hρt : t * conj t = u * conj u) :
    ∀ z ∈ hull K u, Φ (conj z) = conj (Φ z) := by
  have key : ∀ z ∈ hull K u,
      (Φ.comp (starRingEnd ℂ)) z = ((starRingEnd ℂ).comp Φ) z := by
    refine eqOn_hull' _ _ ?_ ?_
    · intro a ha
      simp only [RingHom.coe_comp, Function.comp_apply]
      rw [hK _ (hKconj a ha), hK a ha]
    · simp only [RingHom.coe_comp, Function.comp_apply, hΦu]
      have h1 : conj u = (u * conj u) / u := (conj_eq_rho_div' hu0).symm
      have h2 : conj t = (u * conj u) / t := by
        rw [← hρt]; field_simp
      rw [h1, h2, map_div₀, hK _ hρ, hΦu]
  intro z hz
  simpa using key z hz

/-- **The closure theorem, existence included.** -/
theorem exists_conj_intertwining' {K : Subfield ℂ} {u t : ℂ}
    (hKconj : ∀ a ∈ K, conj a ∈ K)
    (hu : Transcendental (↥K) u) (ht : Transcendental (↥K) t)
    (hρ : u * conj u ∈ K) (hρt : t * conj t = u * conj u) :
    ∃ Φ : ℂ →+* ℂ, (∀ a ∈ K, Φ a = a) ∧ Φ u = t
      ∧ ∀ z ∈ hull K u, Φ (conj z) = conj (Φ z) := by
  obtain ⟨Φ, hK, hΦu⟩ := exists_ringHom_of_transcendental' hu ht
  exact ⟨Φ, hK, hΦu, conj_comm' Φ hK hKconj (transcendental_ne_zero' hu)
    (transcendental_ne_zero' ht) hΦu hρ hρt⟩

/-- **A transcendental point on a circle of positive radius.** Pure counting: the circle is
uncountable and the algebraic points are countable. -/
theorem exists_transcendental_on_circle' {L : Subfield ℂ}
    [Algebra.IsAlgebraic ℚ (↥L)] {r : ℂ} (hr : r ∈ L) (hrc : conj r ∈ L)
    (hr0 : r ≠ 0) :
    ∃ t : ℂ, t ≠ 0 ∧ Transcendental (↥L) t ∧ t * conj t = r * conj r
      ∧ t * conj t ∈ L := by
  classical
  set ρ : ℝ := Complex.normSq r with hρdef
  have hρpos : 0 < ρ := Complex.normSq_pos.2 hr0
  set c : ℝ := Real.sqrt ρ with hcdef
  have hcpos : 0 < c := Real.sqrt_pos.2 hρpos
  have hcsq : c ^ 2 = ρ := Real.sq_sqrt hρpos.le
  set f : ℝ → ℂ := fun x => Complex.mk x (Real.sqrt (ρ - x ^ 2)) with hfdef
  have hfinj : Function.Injective f := by
    intro x y hxy
    have := congrArg Complex.re hxy
    simpa [hfdef] using this
  have hfnorm : ∀ x ∈ Set.Ioo (-c) c, Complex.normSq (f x) = ρ := by
    intro x hx
    have hx2 : x ^ 2 < ρ := by
      rw [← hcsq]
      nlinarith [hx.1, hx.2, hcpos]
    have hs : Real.sqrt (ρ - x ^ 2) * Real.sqrt (ρ - x ^ 2) = ρ - x ^ 2 :=
      Real.mul_self_sqrt (by linarith)
    simp only [Complex.normSq_apply, hfdef]
    nlinarith [hs]
  have hex : ∃ x ∈ Set.Ioo (-c) c, Transcendental ℚ (f x) := by
    by_contra hcon
    push Not at hcon
    have hsub : Set.Ioo (-c) c ⊆ f ⁻¹' {z : ℂ | IsAlgebraic ℚ z} := by
      intro x hx
      have := hcon x hx
      rw [Transcendental, not_not] at this
      exact this
    have hcount : (Set.Ioo (-c) c).Countable :=
      Set.Countable.mono hsub ((Algebraic.countable ℚ ℂ).preimage hfinj)
    rw [Cardinal.Real.Ioo_countable_iff] at hcount
    linarith
  obtain ⟨x, hx, hxt⟩ := hex
  refine ⟨f x, ?_, ?_, ?_, ?_⟩
  · intro hz
    have := hfnorm x hx
    rw [hz] at this
    simp at this
    exact absurd this.symm (ne_of_gt hρpos)
  · exact (Algebra.IsAlgebraic.transcendental_iff (R := ℚ) (S := (↥L))).1 hxt
  · rw [Complex.mul_conj, Complex.mul_conj, hfnorm x hx, ← hρdef]
  · have hcast : ((ρ : ℝ) : ℂ) = r * conj r := (Complex.mul_conj r).symm
    rw [Complex.mul_conj, hfnorm x hx, hcast]
    exact mul_mem hr hrc

/-- The circle condition in the form the matrix results consume. -/
theorem exists_transcendental_on_circle_sq' {L : Subfield ℂ}
    [Algebra.IsAlgebraic ℚ (↥L)] {r : ℂ} (hr : r ∈ L) (hrr : conj r = r)
    (hr0 : r ≠ 0) :
    ∃ t : ℂ, t ≠ 0 ∧ Transcendental (↥L) t ∧ t * conj t = r ^ 2
      ∧ t * conj t ∈ L := by
  obtain ⟨t, ht0, hT, heq, hmem⟩ :=
    exists_transcendental_on_circle' hr (by rw [hrr]; exact hr) hr0
  refine ⟨t, ht0, hT, ?_, hmem⟩
  rw [heq, hrr]; ring

end Diaz

open Diaz in
theorem solution
    {u r : ℂ} (hu0 : u ≠ 0) (hexp : IsAlgebraic ℚ (Complex.exp u))
    (hr : r ∈ Qbar) (hrr : conj r = r) (hr0 : r ≠ 0)
    (h : u * conj u = r ^ 2) :
    ∃ t : ℂ, t ≠ 0 ∧ Transcendental (↥Qbar) t ∧
      ∃ Φ : ℂ →+* ℂ, (∀ a ∈ Qbar, Φ a = a) ∧ Φ u = t
        ∧ ∀ z ∈ hull Qbar u, Φ (conj z) = conj (Φ z) := by
  obtain ⟨t, ht0, hT, hteq, htmem⟩ := exists_transcendental_on_circle_sq' hr hrr hr0
  have hu : Transcendental (↥Qbar) u := transcendental_candidate_over_base' hu0 hexp
  obtain ⟨Φ, hK, hΦu, hcomm⟩ :=
    exists_conj_intertwining' (K := Qbar) (fun a ha => conj_mem_Qbar' ha) hu hT
      (by rw [h]; exact pow_mem hr 2) (by rw [hteq, h])
  exact ⟨t, ht0, hT, Φ, hK, hΦu, hcomm⟩
