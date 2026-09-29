-- Prove2me | solution 1 for Esquisse.belyi_polynomial_defined_over_algebraic_numbers
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-21T04:14:56.838925+00:00
-- url     : https://prove2.me/submissions/ae187682-2e76-44fd-9f05-d6564c022ace

import Mathlib
import Definitions.Def_esquisse_dessins_basic

set_option autoImplicit false

noncomputable section

/- BEGIN discovery_dessins_descent/CoefficientDerivation.lean -/
/-!
Internal draft for existing target 5d30c48e-ae4e-47d7-ae73-bca1e58c4820.
Not compiler checked. No new public component is proposed.

The main multiplicity lemma has an explicit splitting hypothesis. Thus it can
be used over the finitely generated root field, without assuming that field is
algebraically closed (which would destroy the finite-generation argument).
-/


open Polynomial
namespace DessinsDescent

variable {K : Type*} [Field K] [CharZero K]

/-- Coefficient differentiation as an ordinary polynomial-valued derivation. -/
private def coefficientDerivation (D : Derivation ℚ K K) :
    Derivation ℚ K[X] K[X] :=
  PolynomialModule.equivPolynomialSelf.compDer D.mapCoeffs

@[simp] private theorem coefficientDerivation_coeff (D : Derivation ℚ K K)
    (P : K[X]) (i : ℕ) :
    (coefficientDerivation D P).coeff i = D (P.coeff i) := rfl

@[simp] private theorem coefficientDerivation_C (D : Derivation ℚ K K) (a : K) :
    coefficientDerivation D (C a) = C (D a) := by
  ext i
  by_cases hi : i = 0 <;> simp [Polynomial.coeff_C, hi]

/-- A coefficient derivation lowers the multiplicity of any constant-valued
fiber by at most one, with no simple-root assumption. -/
private theorem pow_dvd_coefficientDerivation_of_fiber_pow_dvd
    (D : Derivation ℚ K K) (P : K[X]) (c b : K) (m : ℕ)
    (hb : D b = 0) (hpow : (X - C c) ^ (m + 1) ∣ P - C b) :
    (X - C c) ^ m ∣ coefficientDerivation D P := by
  obtain ⟨R, hR⟩ := hpow
  have hDC : coefficientDerivation D (C b) = 0 := by simp [hb]
  have hDP : coefficientDerivation D P =
      coefficientDerivation D ((X - C c) ^ (m + 1) * R) := by
    rw [← hR, map_sub, hDC, sub_zero]
  rw [hDP, Derivation.leibniz, Derivation.leibniz_pow]
  refine ⟨(X - C c) * coefficientDerivation D R +
    (m + 1 : K[X]) * R * coefficientDerivation D (X - C c), ?_⟩
  simp only [Nat.add_sub_cancel, smul_eq_mul, nsmul_eq_mul, pow_succ,
    Nat.cast_add, Nat.cast_one]
  ring

/-- Exact local bridge, including repeated critical points. If c is critical
of multiplicity m in P', then the fiber through c has multiplicity m+1. -/
private theorem critical_power_dvd_coefficientDerivation
    (D : Derivation ℚ K K) (P : K[X]) (hP' : P.derivative ≠ 0)
    (c : K) (hc : P.derivative.eval c = 0)
    (hvalue : D (P.eval c) = 0) :
    (X - C c) ^ P.derivative.rootMultiplicity c ∣ coefficientDerivation D P := by
  let R := P - C (P.eval c)
  have hRderiv : R.derivative = P.derivative := by simp [R]
  have hR0 : R ≠ 0 := by
    intro hz
    apply hP'
    rw [← hRderiv, hz]
    simp
  have hroot : R.IsRoot c := by simp [R, Polynomial.IsRoot]
  have hrpos : 0 < R.rootMultiplicity c := (Polynomial.rootMultiplicity_pos hR0).mpr hroot
  have hmult : P.derivative.rootMultiplicity c = R.rootMultiplicity c - 1 := by
    rw [← hRderiv]
    exact Polynomial.derivative_rootMultiplicity_of_root hroot
  have hsucc : P.derivative.rootMultiplicity c + 1 = R.rootMultiplicity c := by omega
  apply pow_dvd_coefficientDerivation_of_fiber_pow_dvd D P c (P.eval c)
    (P.derivative.rootMultiplicity c) hvalue
  rw [hsucc]
  exact Polynomial.pow_rootMultiplicity_dvd R c

/-- The central bridge needed for algebraic descent. The derivative must split
in K; this is a mathematical hypothesis, not merely an elaboration convenience.
Every critical value must be annihilated by the chosen coefficient derivation. -/
private theorem derivative_dvd_coefficientDerivation
    (D : Derivation ℚ K K) (P : K[X]) (hP' : P.derivative ≠ 0)
    (hsplit : P.derivative.Splits)
    (hcritical : ∀ c : K, P.derivative.eval c = 0 → D (P.eval c) = 0) :
    P.derivative ∣ coefficientDerivation D P := by
  classical
  by_cases hD0 : coefficientDerivation D P = 0
  · rw [hD0]
    exact dvd_zero _
  apply hsplit.dvd_of_roots_le_roots hP'
  apply Multiset.le_iff_count.mpr
  intro c
  simp only [Polynomial.count_roots]
  apply (Polynomial.le_rootMultiplicity_iff hD0).mpr
  by_cases hc : P.derivative.eval c = 0
  · exact critical_power_dvd_coefficientDerivation D P hP' c hc (hcritical c hc)
  · have hmult : P.derivative.rootMultiplicity c = 0 :=
      Polynomial.rootMultiplicity_eq_zero (by simpa only [Polynomial.IsRoot] using hc)
    simp [hmult]

/-- With the Belyi critical-value condition, zero and one are automatically
annihilated by any rational derivation. This is the literal condition occurring
in `Esquisse.IsBelyiPolynomial`, without importing or altering its definition. -/
private theorem derivative_dvd_coefficientDerivation_of_belyi
    (D : Derivation ℚ K K) (P : K[X]) (hdegree : 0 < P.natDegree)
    (hsplit : P.derivative.Splits)
    (hcritical : ∀ c : K, P.derivative.eval c = 0 → P.eval c = 0 ∨ P.eval c = 1) :
    P.derivative ∣ coefficientDerivation D P := by
  apply derivative_dvd_coefficientDerivation D P
    (Polynomial.derivative_ne_zero.mpr (by omega)) hsplit
  intro c hc
  rcases hcritical c hc with h | h <;> simp [h]

/-- A monic centered Belyi polynomial has coefficients annihilated by every
rational derivation of a field in which its derivative splits. -/
private theorem coefficients_annihilated_of_monic_centered_belyi
    (D : Derivation ℚ K K) (P : K[X]) (hdegree : 0 < P.natDegree)
    (hmonic : P.Monic) (hcenter : P.coeff (P.natDegree - 1) = 0)
    (hsplit : P.derivative.Splits)
    (hcritical : ∀ c : K, P.derivative.eval c = 0 → P.eval c = 0 ∨ P.eval c = 1) :
    ∀ i : ℕ, D (P.coeff i) = 0 := by
  have hdvd := derivative_dvd_coefficientDerivation_of_belyi D P hdegree hsplit hcritical
  have hzero : coefficientDerivation D P = 0 := by
    by_contra hne
    have hle := Polynomial.natDegree_le_of_dvd hdvd hne
    rw [Polynomial.natDegree_derivative] at hle
    have hcoeff : (coefficientDerivation D P).coeff
        (coefficientDerivation D P).natDegree = 0 := by
      rw [coefficientDerivation_coeff]
      by_cases hlt : P.natDegree < (coefficientDerivation D P).natDegree
      · rw [Polynomial.coeff_eq_zero_of_natDegree_lt hlt, map_zero]
      · by_cases heq : (coefficientDerivation D P).natDegree = P.natDegree
        · rw [heq, hmonic.coeff_natDegree, Derivation.map_one_eq_zero]
        · have hpred : (coefficientDerivation D P).natDegree = P.natDegree - 1 := by omega
          rw [hpred, hcenter, map_zero]
    exact hne (Polynomial.leadingCoeff_eq_zero.mp
      (by simpa only [Polynomial.coeff_natDegree] using hcoeff))
  intro i
  have hi := congrArg (fun H : K[X] => H.coeff i) hzero
  simpa only [coefficientDerivation_coeff, Polynomial.coeff_zero] using hi

end DessinsDescent
/- END CoefficientDerivation.lean -/

/- BEGIN discovery_dessins_descent/DerivationAlgebraicity.lean -/
/-!
Internal bridge for the exact complex Belyi-polynomial descent target.
No compiler has been run on this draft. No public component is proposed.

The hypothesis is vanishing of K-valued rational derivations. Triviality of
Kähler differentials is proved using the algebraic dual, not assumed.
Finiteness means finite generation as a FIELD, expressed equivalently by
`Algebra.EssFiniteType`; no finite-dimensional/algebraic premise is inserted.
-/


namespace DessinsDescent

variable {K : Type*} [Field K] [CharZero K]

/-- All K-valued rational derivations vanish, so all linear functionals on the
Kähler differentials vanish; separation by the algebraic dual forces Ω=0. -/
private theorem kaehler_subsingleton_of_derivations_eq_zero
    (hD : ∀ D : Derivation ℚ K K, D = 0) :
    Subsingleton (KaehlerDifferential ℚ K) := by
  let e : (KaehlerDifferential ℚ K →ₗ[K] K) ≃ₗ[K] Derivation ℚ K K :=
    KaehlerDifferential.linearMapEquivDerivation ℚ K
  have hlin : ∀ f : KaehlerDifferential ℚ K →ₗ[K] K, f = 0 := by
    intro f
    apply e.injective
    exact (hD (e f)).trans (map_zero e).symm
  have hzero : ∀ x : KaehlerDifferential ℚ K, x = 0 := by
    intro x
    apply (Module.forall_dual_apply_eq_zero_iff K x).mp
    intro f
    rw [hlin f]
    rfl
  exact ⟨fun x y => (hzero x).trans (hzero y).symm⟩

/-- The pinned unramified-field theorem converts the established Ω=0 into
separability, which includes algebraicity, under finite field generation. -/
private theorem algebraic_of_essFiniteType_of_derivations_eq_zero
    [Algebra.EssFiniteType ℚ K]
    (hD : ∀ D : Derivation ℚ K K, D = 0) :
    Algebra.IsAlgebraic ℚ K := by
  letI : Subsingleton (KaehlerDifferential ℚ K) :=
    kaehler_subsingleton_of_derivations_eq_zero hD
  letI : Algebra.FormallyUnramified ℚ K := ⟨inferInstance⟩
  letI : Algebra.IsSeparable ℚ K :=
    Algebra.FormallyUnramified.isSeparable ℚ K
  infer_instance

/-- Explicit finite-field-generation form, for a field generated by the roots
of a normalized Belyi polynomial and its fiber over one. -/
private theorem algebraic_of_fg_of_derivations_eq_zero
    (hfg : (⊤ : IntermediateField ℚ K).FG)
    (hD : ∀ D : Derivation ℚ K K, D = 0) :
    Algebra.IsAlgebraic ℚ K := by
  letI : Algebra.EssFiniteType ℚ K := IntermediateField.fg_top_iff.mp hfg
  exact algebraic_of_essFiniteType_of_derivations_eq_zero hD

/-- Convenient pointwise interface for the polynomial argument. -/
private theorem algebraic_of_fg_of_derivations_vanish
    (hfg : (⊤ : IntermediateField ℚ K).FG)
    (hD : ∀ (D : Derivation ℚ K K) (x : K), D x = 0) :
    ∀ x : K, IsAlgebraic ℚ x := by
  letI : Algebra.IsAlgebraic ℚ K :=
    algebraic_of_fg_of_derivations_eq_zero hfg (fun D => by
      ext x
      exact hD D x)
  intro x
  exact Algebra.IsAlgebraic.isAlgebraic x

/-- The finite-generator subfield used by descent automatically has the exact
finiteness hypothesis; no algebraicity of its generators is assumed. -/
private theorem adjoin_finset_algebraic_of_derivations_eq_zero
    {E : Type*} [Field E] [CharZero E] (s : Finset E)
    (hD : ∀ D : Derivation ℚ (IntermediateField.adjoin ℚ (s : Set E))
        (IntermediateField.adjoin ℚ (s : Set E)), D = 0) :
    Algebra.IsAlgebraic ℚ (IntermediateField.adjoin ℚ (s : Set E)) := by
  letI : Algebra.EssFiniteType ℚ (IntermediateField.adjoin ℚ (s : Set E)) :=
    IntermediateField.essFiniteType_iff.mpr ⟨s, rfl⟩
  exact algebraic_of_essFiniteType_of_derivations_eq_zero hD

end DessinsDescent
/- END DerivationAlgebraicity.lean -/

/- BEGIN discovery_dessins_descent/RootDerivationDraft.lean -/

/-!
Private root-generation bridge for complex Belyi-polynomial descent.
Draft only: no compiler invocation or public component submission.

Repeated roots are allowed. Taking m-1 formal derivatives at a root of
multiplicity m gives a polynomial with a simple root, while preserving the
property that the rational derivation annihilates every coefficient.
-/


namespace DessinsDescent

open Polynomial

variable {K : Type*} [Field K] [CharZero K]

private theorem rootBridge_derivative_coeff_annihilated
    (D : Derivation ℚ K K) (P : K[X])
    (hcoeff : ∀ i : ℕ, D (P.coeff i) = 0) :
    ∀ i : ℕ, D (P.derivative.coeff i) = 0 := by
  intro i
  rw [coeff_derivative, D.leibniz, hcoeff]
  simp

private theorem rootBridge_iterate_derivative_coeff_annihilated
    (D : Derivation ℚ K K) (P : K[X])
    (hcoeff : ∀ i : ℕ, D (P.coeff i) = 0) (n : ℕ) :
    ∀ i : ℕ, D ((derivative^[n] P).coeff i) = 0 := by
  induction n with
  | zero => exact hcoeff
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact rootBridge_derivative_coeff_annihilated D _ ih

/-- No separability of P is assumed: repeated roots are handled using their
exact multiplicity and characteristic zero. -/
private theorem derivation_root_eq_zero_of_coefficients_eq_zero
    (D : Derivation ℚ K K) (P : K[X]) (hP : P ≠ 0)
    (hcoeff : ∀ i : ℕ, D (P.coeff i) = 0)
    (c : K) (hc : P.eval c = 0) : D c = 0 := by
  let m := P.rootMultiplicity c
  have hmpos : 0 < m := (rootMultiplicity_pos hP).mpr hc
  have hmlt : m - 1 < m := by omega
  have hmsucc : (m - 1).succ = m := by omega
  let Q := derivative^[m - 1] P
  have hQc : Q.eval c = 0 :=
    isRoot_iterate_derivative_of_lt_rootMultiplicity hmlt
  have hcoeffQ : ∀ i : ℕ, D (Q.coeff i) = 0 :=
    rootBridge_iterate_derivative_coeff_annihilated D P hcoeff (m - 1)
  have hQmap : D.mapCoeffs Q = 0 := by
    ext i
    simpa using hcoeffQ i
  have hQderiv : Q.derivative.eval c ≠ 0 := by
    have hiter : Q.derivative = derivative^[m] P := by
      dsimp only [Q]
      rw [← Function.iterate_succ_apply' (f := (derivative : K[X] → K[X])) (n := m - 1) (x := P), hmsucc]
    rw [hiter]
    change (derivative^[P.rootMultiplicity c] P).eval c ≠ 0
    rw [eval_iterate_derivative_rootMultiplicity, nsmul_eq_mul]
    exact mul_ne_zero
      (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _))
      (eval_divByMonic_pow_rootMultiplicity_ne_zero c hP)
  have hchain := D.apply_eval_eq c Q
  have hmul : Q.derivative.eval c * D c = 0 := by
    simpa only [hQc, hQmap, map_zero, zero_add, smul_eq_mul] using hchain.symm
  exact (mul_eq_zero.mp hmul).resolve_left hQderiv

/-- A derivation vanishes on the entire generated field when it vanishes on
the generators. Inverses are part of the induction, not an implicit premise. -/
private theorem derivation_eq_zero_on_adjoin
    (D : Derivation ℚ K K) (S : Set K)
    (hS : ∀ x ∈ S, D x = 0) {x : K}
    (hx : x ∈ IntermediateField.adjoin ℚ S) : D x = 0 := by
  refine IntermediateField.adjoin_induction ℚ
    (p := fun x _ => D x = 0)
    (fun x hx => hS x hx) (fun x => D.map_algebraMap x)
    ?_ ?_ ?_ hx
  · intro x y _ _ hDx hDy
    simp [map_add, hDx, hDy]
  · intro x _ hDx
    simp [D.leibniz_inv, hDx]
  · intro x y _ _ hDx hDy
    simp [D.leibniz, hDx, hDy]

private theorem derivation_eq_zero_of_generators
    (D : Derivation ℚ K K) (S : Set K)
    (hgen : IntermediateField.adjoin ℚ S = ⊤)
    (hS : ∀ x ∈ S, D x = 0) : D = 0 := by
  ext x
  apply derivation_eq_zero_on_adjoin D S hS
  rw [hgen]
  trivial

/-- Direct interface for a finite field-generating family of roots of one or
several nonzero polynomials, all with derivation-constant coefficients. -/
private theorem derivation_eq_zero_of_root_generators
    (D : Derivation ℚ K K) (S : Finset K)
    (hgen : IntermediateField.adjoin ℚ (S : Set K) = ⊤)
    (hroot : ∀ c ∈ S, ∃ P : K[X], P ≠ 0 ∧
      (∀ i : ℕ, D (P.coeff i) = 0) ∧ P.eval c = 0) : D = 0 := by
  apply derivation_eq_zero_of_generators D (S : Set K) hgen
  intro c hc
  obtain ⟨P, hP, hcoeff, hPc⟩ := hroot c hc
  exact derivation_root_eq_zero_of_coefficients_eq_zero D P hP hcoeff c hPc

/-- The original generators, viewed inside their generated subfield, still
generate that entire subfield. This discharges the hgen interface without any
algebraicity assumption on the generators. -/
private theorem rootBridge_adjoin_subtype_generators_eq_top
    {E : Type*} [Field E] [CharZero E] (S : Set E) :
    IntermediateField.adjoin ℚ
      {x : IntermediateField.adjoin ℚ S | (x : E) ∈ S} = ⊤ := by
  apply IntermediateField.lift_injective (IntermediateField.adjoin ℚ S)
  erw [IntermediateField.lift_adjoin, IntermediateField.lift_top]
  have himage : Subtype.val ''
      {x : IntermediateField.adjoin ℚ S | (x : E) ∈ S} = S := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      exact ⟨⟨x, IntermediateField.subset_adjoin ℚ S hx⟩, hx, rfl⟩
  rw [himage]

private theorem derivation_on_adjoin_eq_zero_of_generators
    {E : Type*} [Field E] [CharZero E] (S : Set E)
    (D : Derivation ℚ (IntermediateField.adjoin ℚ S)
      (IntermediateField.adjoin ℚ S))
    (hS : ∀ x : IntermediateField.adjoin ℚ S, (x : E) ∈ S → D x = 0) :
    D = 0 :=
  derivation_eq_zero_of_generators D _
    (rootBridge_adjoin_subtype_generators_eq_top S) hS

end DessinsDescent

/- END RootDerivationDraft.lean -/

/- BEGIN discovery_dessins_faithful/RootFieldDraft.lean -/
namespace DessinsRootField

open Polynomial

/-- The field generated by both finite branch fibres.  This definition does
not assert that the generators, or any coefficients, are algebraic over ℚ. -/
def rootField (Q : ℂ[X]) : IntermediateField ℚ ℂ :=
  IntermediateField.adjoin ℚ
    {z : ℂ | z ∈ Q.roots ∨ z ∈ (Q - 1).roots}

/-- Finite generation as a field, without algebraicity of the generators. -/
theorem rootField_essFiniteType (Q : ℂ[X]) :
    Algebra.EssFiniteType ℚ (rootField Q) := by
  classical
  apply IntermediateField.essFiniteType_iff.mpr
  refine ⟨Q.roots.toFinset ∪ (Q - 1).roots.toFinset, ?_⟩
  unfold rootField
  congr 1
  ext z
  simp only [Finset.mem_coe, Finset.mem_union, Multiset.mem_toFinset,
    Set.mem_setOf_eq]

theorem root_mem_rootField {Q : ℂ[X]} {z : ℂ} (hz : z ∈ Q.roots) :
    z ∈ rootField Q :=
  IntermediateField.subset_adjoin ℚ _ (Or.inl hz)

theorem root_sub_one_mem_rootField {Q : ℂ[X]} {z : ℂ}
    (hz : z ∈ (Q - 1).roots) : z ∈ rootField Q :=
  IntermediateField.subset_adjoin ℚ _ (Or.inr hz)

/-- Monicity makes the coefficients polynomial expressions in the roots;
no algebraicity of those roots is used. -/
theorem monic_mem_lifts_rootField (Q : ℂ[X]) (hmonic : Q.Monic) :
    Q ∈ Polynomial.lifts (rootField Q).val.toRingHom := by
  apply (IsAlgClosed.splits Q).mem_lift_of_roots_mem_range hmonic
  intro z hz
  exact ⟨⟨z, root_mem_rootField hz⟩, rfl⟩

/-- Critical points belong to one of the two branch fibres.  The positive
degree hypothesis excludes `Q = 1`, so the second polynomial's root multiset
faithfully records all points of its zero fibre. -/
theorem critical_root_mem_rootField (Q : ℂ[X]) (hdegree : 0 < Q.natDegree)
    (hmonic : Q.Monic)
    (hcrit : ∀ z : ℂ, Q.derivative.eval z = 0 → Q.eval z = 0 ∨ Q.eval z = 1)
    {z : ℂ} (hz : Q.derivative.eval z = 0) : z ∈ rootField Q := by
  rcases hcrit z hz with hz0 | hz1
  · apply root_mem_rootField
    exact (Polynomial.mem_roots hmonic.ne_zero).2 hz0
  · have hne : Q - 1 ≠ 0 := by
      apply sub_ne_zero.mpr
      intro h
      simp only [h, natDegree_one] at hdegree
      omega
    apply root_sub_one_mem_rootField
    apply (Polynomial.mem_roots hne).2
    change (Q - 1).eval z = 0
    simp only [eval_sub, eval_one, hz1, sub_self]

/-- A monic complex Belyi polynomial descends to the field generated by its
zero and one fibres.  Both fibres and the derivative split over that field.
This is a root-field statement, not yet descent to algebraic numbers. -/
theorem exists_rootField_lift (Q : ℂ[X]) (hdegree : 0 < Q.natDegree)
    (hmonic : Q.Monic)
    (hcrit : ∀ z : ℂ, Q.derivative.eval z = 0 → Q.eval z = 0 ∨ Q.eval z = 1) :
    ∃ q : (rootField Q)[X],
      q.map (rootField Q).val.toRingHom = Q ∧
      q.natDegree = Q.natDegree ∧ q.Monic ∧
      q.Splits ∧ (q - 1).Splits ∧ q.derivative.Splits := by
  obtain ⟨q, hq, hdeg, hmon⟩ :=
    Polynomial.lifts_and_natDegree_eq_and_monic
      (monic_mem_lifts_rootField Q hmonic) hmonic
  refine ⟨q, hq, hdeg, hmon, ?_, ?_, ?_⟩
  · apply Polynomial.Splits.of_splits_map (rootField Q).val.toRingHom
      (IsAlgClosed.splits (q.map (rootField Q).val.toRingHom))
    intro z hz
    rw [hq] at hz
    exact ⟨⟨z, root_mem_rootField hz⟩, rfl⟩
  · apply Polynomial.Splits.of_splits_map (rootField Q).val.toRingHom
      (IsAlgClosed.splits ((q - 1).map (rootField Q).val.toRingHom))
    intro z hz
    rw [Polynomial.map_sub, Polynomial.map_one, hq] at hz
    exact ⟨⟨z, root_sub_one_mem_rootField hz⟩, rfl⟩
  · apply Polynomial.Splits.of_splits_map (rootField Q).val.toRingHom
      (IsAlgClosed.splits (q.derivative.map (rootField Q).val.toRingHom))
    intro z hz
    have hdmap : q.derivative.map (rootField Q).val.toRingHom = Q.derivative := by
      rw [← Polynomial.derivative_map, hq]
    rw [hdmap] at hz
    have heval : Q.derivative.eval z = 0 := ((Polynomial.mem_roots').mp hz).2
    exact ⟨⟨z, critical_root_mem_rootField Q hdegree hmonic hcrit heval⟩, rfl⟩

end DessinsRootField
/- END RootFieldDraft.lean -/

/- BEGIN discovery_dessins_descent/AffineNormalizationDraft.lean -/
/-!
Private source-affine normalization for the exact complex Belyi descent target.
This draft has not been compiled. There is no target-affine transformation and
no algebraicity assumption on any input coefficient.
-/


namespace DessinsDescent

open Polynomial

/-- A source translation centers a positive-degree complex polynomial.
The Hasse derivative of order n-1 has degree one, including the n=1 case. -/
private theorem exists_centering_translation
    (P : ℂ[X]) (hdegree : 0 < P.natDegree) :
    ∃ b : ℂ, (taylor b P).coeff (P.natDegree - 1) = 0 := by
  have hHdegree : (hasseDeriv (P.natDegree - 1) P).natDegree = 1 := by
    rw [natDegree_hasseDeriv]
    omega
  have hHpos : 0 < (hasseDeriv (P.natDegree - 1) P).natDegree := by
    rw [hHdegree]
    exact Nat.zero_lt_one
  obtain ⟨b, hb⟩ := IsAlgClosed.exists_root
    (hasseDeriv (P.natDegree - 1) P)
    (ne_of_gt (natDegree_pos_iff_degree_pos.mp hHpos))
  refine ⟨b, ?_⟩
  rw [taylor_coeff]
  exact hb

/-- The complete normalization interface, stated with the literal critical
value condition to avoid duplicating or importing platform definitions.

The first three output clauses are precisely a witness for
`Esquisse.AffineEquivalent P Q` in its actual orientation. -/
private theorem exists_monic_centered_source_affine_belyi
    (P : ℂ[X]) (hdegree : 0 < P.natDegree)
    (hcrit : ∀ z : ℂ, P.derivative.eval z = 0 →
      P.eval z = 0 ∨ P.eval z = 1) :
    ∃ (Q : ℂ[X]) (a b : ℂ), a ≠ 0 ∧
      Q = P.comp (C a * X + C b) ∧
      Q.natDegree = P.natDegree ∧ Q.Monic ∧
      Q.coeff (Q.natDegree - 1) = 0 ∧
      (∀ z : ℂ, Q.derivative.eval z = 0 →
        Q.eval z = 0 ∨ Q.eval z = 1) := by
  have hP : P ≠ 0 := by
    intro h
    simp [h] at hdegree
  have hlc : P.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hP
  obtain ⟨b, hb⟩ := exists_centering_translation P hdegree
  obtain ⟨a, ha⟩ := IsAlgClosed.exists_pow_nat_eq
    P.leadingCoeff⁻¹ hdegree
  have ha0 : a ≠ 0 := by
    intro h
    rw [h, zero_pow (Nat.ne_of_gt hdegree)] at ha
    exact (inv_ne_zero hlc) ha.symm
  let Q : ℂ[X] := (taylor b P).comp (C a * X)
  have hQaffine : Q = P.comp (C a * X + C b) := by
    simp only [Q, taylor_apply, comp_assoc, add_comp, X_comp, C_comp]
  have hQdegree : Q.natDegree = P.natDegree := by
    dsimp only [Q]
    rw [natDegree_comp, natDegree_taylor, natDegree_C_mul_X a ha0, mul_one]
  have hQmonic : Q.Monic := by
    change Q.leadingCoeff = 1
    dsimp only [Q]
    rw [leadingCoeff_comp (by rw [natDegree_C_mul_X a ha0]; decide),
      leadingCoeff_taylor, leadingCoeff_C_mul_X, natDegree_taylor, ha,
      mul_inv_cancel₀ hlc]
  have hQcenter : Q.coeff (Q.natDegree - 1) = 0 := by
    rw [hQdegree]
    change ((taylor b P).comp (C a * X)).coeff (P.natDegree - 1) = 0
    rw [comp_C_mul_X_coeff, hb, zero_mul]
  refine ⟨Q, a, b, ha0, hQaffine, hQdegree, hQmonic, hQcenter, ?_⟩
  intro z hz
  have hchain : a * P.derivative.eval (a * z + b) = 0 := by
    simpa [hQaffine, derivative_comp] using hz
  have hPcrit : P.derivative.eval (a * z + b) = 0 :=
    (mul_eq_zero.mp hchain).resolve_left ha0
  simpa [hQaffine] using hcrit (a * z + b) hPcrit

end DessinsDescent
/- END AffineNormalizationDraft.lean -/

/- BEGIN discovery_dessins_descent/DescentAssembly.lean -/
/-! Final private assembly; inlined into DescentProof.lean. -/

namespace DessinsDescent

open Polynomial

private theorem monic_centered_belyi_coefficients_algebraic
    (Q : ℂ[X]) (hdegree : 0 < Q.natDegree) (hmonic : Q.Monic)
    (hcenter : Q.coeff (Q.natDegree - 1) = 0)
    (hcrit : ∀ z : ℂ, Q.derivative.eval z = 0 →
      Q.eval z = 0 ∨ Q.eval z = 1) :
    ∀ n : ℕ, IsAlgebraic ℚ (Q.coeff n) := by
  let K : IntermediateField ℚ ℂ := IntermediateField.adjoin ℚ
    {z : ℂ | z ∈ Q.roots ∨ z ∈ (Q - 1).roots}
  let φ : K →+* ℂ := K.val.toRingHom
  have hlift : ∃ q : K[X], q.map φ = Q ∧
      q.natDegree = Q.natDegree ∧ q.Monic ∧
      q.Splits ∧ (q - 1).Splits ∧ q.derivative.Splits := by
    exact DessinsRootField.exists_rootField_lift Q hdegree hmonic hcrit
  obtain ⟨q, hq, hdeg, hmon, _hsplit, _hsubsplit, hdersplit⟩ := hlift
  have hqdeg : 0 < q.natDegree := by omega
  have hcoeffmap (n : ℕ) : φ (q.coeff n) = Q.coeff n := by
    exact (Polynomial.coeff_map (p := q) (f := φ) n).symm.trans
      (congrArg (fun R : ℂ[X] => R.coeff n) hq)
  have hqcenter : q.coeff (q.natDegree - 1) = 0 := by
    apply φ.injective
    rw [map_zero, hcoeffmap, hdeg]
    exact hcenter
  have heval (x : K) : Q.eval (x : ℂ) = φ (q.eval x) := by
    calc
      Q.eval (x : ℂ) = (q.map φ).eval (φ x) :=
        (congrArg (fun R : ℂ[X] => R.eval (φ x)) hq).symm
      _ = φ (q.eval x) := Polynomial.eval_map_apply (p := q) (f := φ) x
  have hdmap : q.derivative.map φ = Q.derivative := by
    exact (Polynomial.derivative_map q φ).symm.trans
      (congrArg Polynomial.derivative hq)
  have hdeval (x : K) : Q.derivative.eval (x : ℂ) = φ (q.derivative.eval x) := by
    calc
      Q.derivative.eval (x : ℂ) = (q.derivative.map φ).eval (φ x) :=
        (congrArg (fun R : ℂ[X] => R.eval (φ x)) hdmap).symm
      _ = φ (q.derivative.eval x) :=
        Polynomial.eval_map_apply (p := q.derivative) (f := φ) x
  have hqcrit : ∀ x : K, q.derivative.eval x = 0 →
      q.eval x = 0 ∨ q.eval x = 1 := by
    intro x hx
    have hxc : Q.derivative.eval (x : ℂ) = 0 := by
      rw [hdeval, hx, map_zero]
    rcases hcrit (x : ℂ) hxc with hzero | hone
    · left
      apply φ.injective
      rw [map_zero, ← heval]
      exact hzero
    · right
      apply φ.injective
      rw [map_one, ← heval]
      exact hone
  have hQsub : Q - 1 ≠ 0 := by
    intro h
    have hQone := sub_eq_zero.mp h
    simp [hQone] at hdegree
  have hqsub : q - 1 ≠ 0 := by
    intro h
    have hqone := sub_eq_zero.mp h
    simp [hqone] at hqdeg
  have hD : ∀ D : Derivation ℚ K K, D = 0 := by
    intro D
    have hcoeff : ∀ n : ℕ, D (q.coeff n) = 0 :=
      coefficients_annihilated_of_monic_centered_belyi D q hqdeg
        hmon hqcenter hdersplit hqcrit
    have hsubcoeff : ∀ n : ℕ, D ((q - 1).coeff n) = 0 := by
      intro n
      by_cases hn : n = 0 <;>
        simp [Polynomial.coeff_sub, Polynomial.coeff_one, hn, hcoeff]
    apply derivation_on_adjoin_eq_zero_of_generators
      {z : ℂ | z ∈ Q.roots ∨ z ∈ (Q - 1).roots} D
    intro x hx
    rcases hx with hxzero | hxone
    · have hrootC : Q.eval (x : ℂ) = 0 :=
        (Polynomial.mem_roots hmonic.ne_zero).mp hxzero
      have hrootK : q.eval x = 0 := by
        apply φ.injective
        rw [map_zero, ← heval]
        exact hrootC
      exact derivation_root_eq_zero_of_coefficients_eq_zero D q hmon.ne_zero
        hcoeff x hrootK
    · have hrootC : (Q - 1).eval (x : ℂ) = 0 :=
        (Polynomial.mem_roots hQsub).mp hxone
      have hvalueC : Q.eval (x : ℂ) = 1 := by
        apply sub_eq_zero.mp
        simpa only [Polynomial.eval_sub, Polynomial.eval_one] using hrootC
      have hvalueK : q.eval x = 1 := by
        apply φ.injective
        rw [map_one, ← heval]
        exact hvalueC
      have hrootK : (q - 1).eval x = 0 := by
        simp only [Polynomial.eval_sub, Polynomial.eval_one, hvalueK, sub_self]
      exact derivation_root_eq_zero_of_coefficients_eq_zero D (q - 1) hqsub
        hsubcoeff x hrootK
  letI : Algebra.EssFiniteType ℚ K := by
    exact DessinsRootField.rootField_essFiniteType Q
  letI : Algebra.IsAlgebraic ℚ K :=
    algebraic_of_essFiniteType_of_derivations_eq_zero hD
  intro n
  have hcoeff_alg : IsAlgebraic ℚ (q.coeff n) :=
    Algebra.IsAlgebraic.isAlgebraic (q.coeff n)
  have halg : IsAlgebraic ℚ (φ (q.coeff n)) :=
    hcoeff_alg.algHom φ.toRatAlgHom
  simpa only [hcoeffmap n] using halg

end DessinsDescent

/-- Exact existing platform target, using its unchanged public definitions. -/
theorem solution (P : Polynomial ℂ) (hP : Esquisse.IsBelyiPolynomial P) :
    ∃ Q : Polynomial ℂ, Esquisse.AffineEquivalent P Q ∧
      ∀ n : ℕ, IsAlgebraic ℚ (Q.coeff n) := by
  obtain ⟨Q, a, b, ha, hQ, hdeg, hmon, hcenter, hcrit⟩ :=
    DessinsDescent.exists_monic_centered_source_affine_belyi P hP.1 hP.2
  refine ⟨Q, ⟨a, b, ha, hQ⟩, ?_⟩
  exact DessinsDescent.monic_centered_belyi_coefficients_algebraic Q
    (by rw [hdeg]; exact hP.1) hmon hcenter hcrit

#print axioms solution

/- END DescentAssembly.lean -/

#print axioms solution

end
