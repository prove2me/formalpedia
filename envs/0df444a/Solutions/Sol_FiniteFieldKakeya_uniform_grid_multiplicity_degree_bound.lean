-- Prove2me | solution 1 for FiniteFieldKakeya.uniform_grid_multiplicity_degree_bound
-- status  : ACCEPTED   (prove)
-- author  : @xwh
-- created : 2026-10-23T06:23:25.031433+00:00
-- url     : https://prove2.me/submissions/bd09dc79-e090-4a50-90e5-1f29b34ca329

import Mathlib
import Definitions.Def_FCP_Kakeya


namespace FCP.Kakeya.GridFactor

open MvPolynomial

/-- Translation fixes the finite-field grid polynomial in every coordinate. -/
theorem grid_translate {F σ : Type*} [Field F] [Fintype F] (i : σ) (a : σ → F) :
    eval₂ C (fun j => X j + C (a j))
      (X i ^ Fintype.card F - X i : MvPolynomial σ F) =
      X i ^ Fintype.card F - X i := by
  have hadd := (FiniteField.frobeniusAlgHom F (MvPolynomial σ F)).map_add (X i) (C (a i))
  change (X i + C (a i)) ^ Fintype.card F =
    X i ^ Fintype.card F + (C (a i)) ^ Fintype.card F at hadd
  simp only [eval₂_sub, eval₂_pow, eval₂_X]
  rw [hadd, ← map_pow, FiniteField.pow_card]
  ring

private theorem grid_polynomial_eq_prod {F : Type*} [Field F] [Fintype F] :
    (Polynomial.X ^ Fintype.card F - Polynomial.X : Polynomial F) =
      ∏ c : F, (Polynomial.X - Polynomial.C c) := by
  classical
  have hm : (Polynomial.X ^ Fintype.card F - Polynomial.X : Polynomial F).Monic :=
    Polynomial.monic_X_pow_sub (by
      simpa using (show (1 : WithBot ℕ) < (Fintype.card F : WithBot ℕ) from
        WithBot.coe_lt_coe.mpr Fintype.one_lt_card))
  have hh := Polynomial.prod_multiset_X_sub_C_of_monic_of_roots_card_eq hm (by
    rw [FiniteField.roots_X_pow_card_sub_X,
      FiniteField.X_pow_card_sub_X_natDegree_eq F Fintype.one_lt_card]
    exact Finset.card_univ)
  simpa only [FiniteField.roots_X_pow_card_sub_X, Finset.prod_map_val] using hh.symm

private theorem eval_finSuccEquiv_C {F : Type*} [Field F] (d : ℕ)
    (P : MvPolynomial (Fin (d + 1)) F) (c : F) :
    Polynomial.eval (C c) (finSuccEquiv F d P) =
      eval₂ C (Fin.cases (C c) (fun j : Fin d => X j)) P := by
  rw [finSuccEquiv_apply, coe_eval₂Hom, polynomial_eval_eval₂]
  congr 1
  · ext a
    simp
  · funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp

/-- If every coordinate hyperplane restriction vanishes identically, the grid factor divides. -/
theorem grid_dvd_of_restrictions_zero {F : Type*} [Field F] [Fintype F]
    (d : ℕ) (P : MvPolynomial (Fin (d + 1)) F)
    (hrest : ∀ c : F, eval₂ C (Fin.cases (C c) (fun j : Fin d => X j)) P = 0) :
    (X (0 : Fin (d + 1)) ^ Fintype.card F - X 0) ∣ P := by
  classical
  let R := MvPolynomial (Fin d) F
  have hdiv (c : F) : (Polynomial.X - Polynomial.C (C c) : Polynomial R) ∣
      finSuccEquiv F d P := by
    rw [Polynomial.dvd_iff_isRoot, Polynomial.IsRoot.def, eval_finSuccEquiv_C]
    exact hrest c
  have hcop : Pairwise (fun a b : F => IsCoprime
      (Polynomial.X - Polynomial.C (C a) : Polynomial R)
      (Polynomial.X - Polynomial.C (C b))) := by
    intro a b hab
    apply Polynomial.isCoprime_X_sub_C_of_isUnit_sub
    simpa only [map_sub] using
      (isUnit_iff_ne_zero.mpr (sub_ne_zero.mpr hab)).map (C : F →+* R)
  have hprod := Fintype.prod_dvd_of_coprime hcop hdiv
  have hprodEq : (∏ c : F, (Polynomial.X - Polynomial.C (C c) : Polynomial R)) =
      Polynomial.X ^ Fintype.card F - Polynomial.X := by
    have hh := congrArg (Polynomial.map (C : F →+* R)) (grid_polynomial_eq_prod (F := F))
    simpa only [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X,
      Polynomial.map_prod, Polynomial.map_C] using hh.symm
  rw [hprodEq] at hprod
  obtain ⟨Q, hQ⟩ := hprod
  refine ⟨(finSuccEquiv F d).symm Q, ?_⟩
  apply (finSuccEquiv F d).injective
  simpa only [map_mul, map_sub, map_pow, finSuccEquiv_X_zero,
    AlgEquiv.apply_symm_apply] using hQ

end FCP.Kakeya.GridFactor


namespace FCP.Kakeya.MultiplicityProof

open MvPolynomial

/-- All coefficients below the specified total order vanish. -/
def LowZero {σ R : Type*} [CommSemiring R] (P : MvPolynomial σ R) (r : ℕ) : Prop :=
  ∀ i : σ →₀ ℕ, i.degree < r → coeff i P = 0

noncomputable def shift {σ R : Type*} [CommSemiring R] (a : σ → R) :
    MvPolynomial σ R →+* MvPolynomial σ R :=
  eval₂Hom C (fun j => X j+C (a j))

/-- Dividing the grid polynomial lowers the vanishing order by at most one. -/
lemma lowZero_grid_quotient {σ R : Type*} [CommRing R] (j : σ) (q r : ℕ)
    (hq : 1 < q) (P : MvPolynomial σ R)
    (h : LowZero ((X j ^ q-X j)*P) (r+1)) : LowZero P r := by
  classical
  intro m hm
  induction hd : m.degree using Nat.strong_induction_on generalizing m with
  | h d ih =>
    have hm' : (Finsupp.single j 1+m).degree < r+1 := by
      simp only [map_add,Finsupp.degree_single]
      omega
    have hh := h _ hm'
    rw [sub_mul,coeff_sub,coeff_X_mul] at hh
    have hz : coeff (Finsupp.single j 1+m) (X j ^ q*P) = 0 := by
      rw [X_pow_eq_monomial,coeff_monomial_mul']
      split_ifs with hle
      · simp only [one_mul]
        have heq := congrArg Finsupp.degree (tsub_add_cancel_of_le hle)
        simp only [map_add,Finsupp.degree_single] at heq
        apply ih _ (by omega) _ (by omega) rfl
      · rfl
    rw [hz] at hh
    exact neg_eq_zero.mp (by simpa using hh)

lemma totalDegree_eval₂_le {σ τ R : Type*} [CommSemiring R]
    (f : σ → MvPolynomial τ R) (hf : ∀ j, (f j).totalDegree ≤ 1)
    (P : MvPolynomial σ R) : (eval₂ C f P).totalDegree ≤ P.totalDegree := by
  classical
  rw [eval₂_eq]
  apply totalDegree_finsetSum_le
  intro m hm
  calc
    (C (coeff m P) * ∏ j ∈ m.support, f j ^ m j).totalDegree
        ≤ 0 + (∏ j ∈ m.support, f j ^ m j).totalDegree := by
          simpa only [totalDegree_C] using totalDegree_mul (C (coeff m P)) _
    _ ≤ ∑ j ∈ m.support, (f j ^ m j).totalDegree := by
      simpa only [zero_add] using totalDegree_finsetProd m.support _
    _ ≤ ∑ j ∈ m.support, m j := by
      apply Finset.sum_le_sum
      intro j hj
      exact (totalDegree_pow _ _).trans (by simpa using Nat.mul_le_mul_left (m j) (hf j))
    _ ≤ P.totalDegree := le_totalDegree hm

noncomputable def restrict {R : Type*} [CommSemiring R] {d : ℕ} (c : R) :
    MvPolynomial (Fin (d+1)) R →+* MvPolynomial (Fin d) R :=
  eval₂Hom C (Fin.cases (C c) (fun j => X j))

@[simp] lemma restrict_C {R : Type*} [CommSemiring R] {d : ℕ} (c x : R) :
    restrict (d := d) c (C x) = C x := by simp [restrict]

@[simp] lemma restrict_X_zero {R : Type*} [CommSemiring R] {d : ℕ} (c : R) :
    restrict (d := d) c (X 0) = C c := by simp [restrict]

@[simp] lemma restrict_X_succ {R : Type*} [CommSemiring R] {d : ℕ} (c : R) (j : Fin d) :
    restrict c (X j.succ) = X j := by simp [restrict]

@[simp] lemma shift_C {σ R : Type*} [CommSemiring R] (a : σ → R) (x : R) :
    shift a (C x) = C x := by simp [shift]

@[simp] lemma shift_X {σ R : Type*} [CommSemiring R] (a : σ → R) (j : σ) :
    shift a (X j) = X j+C (a j) := by simp [shift]

lemma restrict_totalDegree_le {R : Type*} [CommSemiring R] [Nontrivial R] {d : ℕ}
    (c : R) (P : MvPolynomial (Fin (d+1)) R) :
    (restrict c P).totalDegree ≤ P.totalDegree := by
  apply totalDegree_eval₂_le
  intro j
  refine Fin.cases ?_ (fun k => ?_) j <;> simp

lemma shift_restrict {R : Type*} [CommSemiring R] {d : ℕ} (a : Fin d → R) (c : R)
    (P : MvPolynomial (Fin (d+1)) R) :
    shift a (restrict c P) = restrict 0 (shift (Fin.cons c a) P) := by
  have hh : (shift a).comp (restrict c) = (restrict 0).comp (shift (Fin.cons c a)) := by
    apply MvPolynomial.ringHom_ext
    · intro x
      simp
    · intro j
      refine Fin.cases ?_ (fun k => ?_) j <;> simp
  exact DFunLike.congr_fun hh P

lemma coeff_restrict_zero {R : Type*} [CommSemiring R] {d : ℕ}
    (P : MvPolynomial (Fin (d+1)) R) (m : Fin d →₀ ℕ) :
    coeff m (restrict 0 P) = coeff (m.cons 0) P := by
  have hh : restrict (d := d) (0 : R) =
      (Polynomial.evalRingHom (0 : MvPolynomial (Fin d) R)).comp
        (finSuccEquiv R d).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro x
      simp [finSuccEquiv_apply]
    · intro j
      refine Fin.cases ?_ (fun k => ?_) j <;>
        simp [finSuccEquiv_X_zero,finSuccEquiv_X_succ]
  rw [DFunLike.congr_fun hh P]
  change coeff m (((finSuccEquiv R d P).eval 0)) = _
  rw [← Polynomial.coeff_zero_eq_eval_zero]
  exact finSuccEquiv_coeff_coeff m P 0

lemma lowZero_restrict {R : Type*} [CommSemiring R] {d : ℕ} (r : ℕ)
    (P : MvPolynomial (Fin (d+1)) R) (c : R)
    (h : ∀ a, LowZero (shift a P) r) : ∀ a, LowZero (shift a (restrict c P)) r := by
  intro a m hm
  rw [shift_restrict,coeff_restrict_zero]
  apply h
  change (m.cons 0).sum (fun _ e => e) < r
  change m.sum (fun _ e => e) < r at hm
  simpa only [Finsupp.sum_cons,zero_add] using hm

lemma grid_totalDegree {σ R : Type*} [CommRing R] [Nontrivial R] (j : σ) (q : ℕ)
    (hq : 1 < q) : (X j ^ q-X j : MvPolynomial σ R).totalDegree = q := by
  rw [sub_eq_add_neg,totalDegree_add_eq_left_of_totalDegree_lt]
  · exact totalDegree_X_pow _ _
  · simpa only [totalDegree_neg,totalDegree_X,totalDegree_X_pow] using hq

lemma grid_ne_zero {σ R : Type*} [CommRing R] [Nontrivial R] (j : σ) (q : ℕ)
    (hq : 1 < q) : (X j ^ q-X j : MvPolynomial σ R) ≠ 0 := by
  intro hz
  have hh := grid_totalDegree (R := R) j q hq
  rw [hz,totalDegree_zero] at hh
  omega

end FCP.Kakeya.MultiplicityProof


namespace FCP.Kakeya.MultiplicityProof

open MvPolynomial

lemma eq_zero_of_grid_identities {F : Type*} [Field F] [Fintype F]
    (hgrid : ∀ (d : ℕ) (P : MvPolynomial (Fin (d+1)) F),
      (∀ c : F, restrict c P = 0) → (X 0 ^ Fintype.card F-X 0) ∣ P)
    (hshift : ∀ (d : ℕ) (a : Fin (d+1) → F),
      shift a (X 0 ^ Fintype.card F-X 0) = X 0 ^ Fintype.card F-X 0)
    (d r : ℕ) (P : MvPolynomial (Fin d) F)
    (hjet : ∀ a, LowZero (shift a P) r)
    (hdeg : P.totalDegree < r*Fintype.card F) : P = 0 := by
  classical
  induction d generalizing r with
  | zero =>
    have hr : 0 < r := by
      by_contra hh
      have : r = 0 := by omega
      simp [this] at hdeg
    have hh := hjet (fun j => Fin.elim0 j) 0 (by simpa using hr)
    rw [P.eq_C_of_isEmpty] at hh ⊢
    simpa using hh
  | succ d ihd =>
    induction r generalizing P with
    | zero => simp at hdeg
    | succ r ihr =>
      have hrst : ∀ c : F, restrict c P = 0 := by
        intro c
        exact ihd (r+1) (restrict c P) (lowZero_restrict (r+1) P c hjet)
          ((restrict_totalDegree_le c P).trans_lt hdeg)
      obtain ⟨Q,hQ⟩ := hgrid d P hrst
      by_cases hQzero : Q = 0
      · simpa [hQzero] using hQ
      have hjetQ : ∀ a, LowZero (shift a Q) r := by
        intro a
        apply lowZero_grid_quotient 0 (Fintype.card F) r Fintype.one_lt_card
        rw [← hshift d a,← map_mul,← hQ]
        exact hjet a
      have hdegree : P.totalDegree = Fintype.card F+Q.totalDegree := by
        rw [hQ,totalDegree_mul_of_isDomain
          (grid_ne_zero (R := F) (0 : Fin (d+1)) _ Fintype.one_lt_card) hQzero,
          grid_totalDegree _ _ Fintype.one_lt_card]
      have hdegQ : Q.totalDegree < r*Fintype.card F := by
        rw [hdegree,Nat.succ_mul] at hdeg
        omega
      rw [hQ,ihr Q hjetQ hdegQ,mul_zero]

end FCP.Kakeya.MultiplicityProof

namespace FCP.Kakeya.MultiplicityProof

/-- The finite-field multiplicity Schwartz–Zippel bound, using translated coefficients. -/
theorem multiplicity_schwartz_zippel {F : Type*} [Field F] [Fintype F]
    (d r : ℕ) (P : MvPolynomial (Fin d) F) (hP : P ≠ 0)
    (hjet : ∀ a : Fin d → F, ∀ i : Fin d →₀ ℕ,
      i.sum (fun _ e => e) < r →
        MvPolynomial.coeff i (MvPolynomial.eval₂ MvPolynomial.C
          (fun j => MvPolynomial.X j + MvPolynomial.C (a j)) P) = 0) :
    r * Fintype.card F ≤ P.totalDegree := by
  apply Nat.le_of_not_lt
  intro hdeg
  apply hP
  apply eq_zero_of_grid_identities
    (fun d P hrest => GridFactor.grid_dvd_of_restrictions_zero d P hrest)
    (fun d a => GridFactor.grid_translate (0 : Fin (d+1)) a) d r P _ hdeg
  intro a i hi
  exact hjet a i hi

end FCP.Kakeya.MultiplicityProof

/-- A polynomial vanishing to order r at every finite-field point has degree at least rq. -/
theorem solution {F : Type*} [Field F] [Fintype F]
    (d r : ℕ) (P : MvPolynomial (Fin d) F) (hP : P ≠ 0)
    (hjet : ∀ a : Fin d → F, ∀ i : Fin d →₀ ℕ,
      i.sum (fun _ e => e) < r →
        MvPolynomial.coeff i (MvPolynomial.eval₂ MvPolynomial.C
          (fun j => MvPolynomial.X j + MvPolynomial.C (a j)) P) = 0) :
    r * Fintype.card F ≤ P.totalDegree :=
  FCP.Kakeya.MultiplicityProof.multiplicity_schwartz_zippel d r P hP hjet
