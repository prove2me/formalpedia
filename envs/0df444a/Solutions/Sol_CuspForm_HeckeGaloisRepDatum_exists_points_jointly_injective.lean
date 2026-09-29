-- Prove2me | solution 1 for CuspForm.HeckeGaloisRepDatum.exists_points_jointly_injective
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/79d81109-ae2a-5a52-bee7-5e92fa68c6a7

import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.DiscreteValuationRing.TFAE
import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian
import Mathlib.RingTheory.Ideal.MinimalPrime.Localization
import Mathlib.RingTheory.Algebraic.Integral
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
import Mathlib.RingTheory.Finiteness.Cardinality
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.LocalRing.Module
import Mathlib.RingTheory.LocalRing.RingHom.Basic
import Mathlib.Algebra.CharP.Algebra
import Mathlib.LinearAlgebra.Semisimple
import Mathlib.FieldTheory.Perfect
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.LinearAlgebra.FreeModule.PID
import Definitions.Def_CuspForm_HeckeGaloisRepDatum
import Theorems.Thm_IsLocalRing_isAdicComplete_of_module_finite
import Theorems.Thm_IsLocalRing_of_isDomain_of_moduleFinite_of_isAdicComplete
import Theorems.Thm_CuspForm_isReduced_heckeAlgebra_of_primeFactors_subset
import Theorems.Thm_CuspForm_moduleFinite_heckeAlgebra_two
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspForm_HeckeGaloisRepDatum_exists_points_jointly_injective
p2m_attr_erase "simp" "PowerSeries.coeff_heckeV PowerSeries.coeff_heckeU"

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Polynomial

namespace K6Points

section Part1

variable {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [CharZero 𝒪]
  {T : Type} [CommRing T] [Algebra 𝒪 T] [Module.Free 𝒪 T] [Module.Finite 𝒪 T]

theorem isReduced_of_free_of_adjoin_eq_top (G : Set T) (hadj : Algebra.adjoin 𝒪 G = ⊤)
    (hG : ∀ g ∈ G, ∃ P : ℤ[X], Squarefree (P.map (Int.castRingHom ℚ)) ∧ aeval g P = 0) :
    IsReduced T := by
  classical
  let K := FractionRing 𝒪
  haveI : CharZero K := charZero_of_injective_algebraMap (IsFractionRing.injective 𝒪 K)
  let ι := Module.Free.ChooseBasisIndex 𝒪 T
  let b : Module.Basis ι 𝒪 T := Module.Free.chooseBasis 𝒪 T

  let Φ : T →ₐ[𝒪] Matrix ι ι K :=
    ((Algebra.ofId 𝒪 K).mapMatrix.comp
      (LinearMap.toMatrixAlgEquiv b : Module.End 𝒪 T ≃ₐ[𝒪] Matrix ι ι 𝒪).toAlgHom).comp
      (Algebra.lmul 𝒪 T)
  have hΦ : Function.Injective Φ := by
    refine (Matrix.map_injective (IsFractionRing.injective 𝒪 K)).comp
      ((LinearMap.toMatrixAlgEquiv b).injective.comp (Algebra.lmul_injective (R := 𝒪) (A := T)))

  let Ψ : T →+* Module.End K (ι → K) :=
    (Matrix.toLinAlgEquiv' : Matrix ι ι K ≃ₐ[K] Module.End K (ι → K)).toRingEquiv.toRingHom.comp
      Φ.toRingHom
  have hΨ : ∀ x, Ψ x = Matrix.toLin' (Φ x) := fun x => rfl
  have hΨinj : Function.Injective Ψ :=
    (Matrix.toLinAlgEquiv' : Matrix ι ι K ≃ₐ[K] Module.End K (ι → K)).injective.comp hΦ

  have hΨc : ∀ x y, Commute (Ψ x) (Ψ y) := fun x y => by
    rw [Commute, SemiconjBy, ← map_mul, ← map_mul, mul_comm]
  have hss : ∀ x, (Ψ x).IsSemisimple := by
    intro x
    have hx : x ∈ Algebra.adjoin 𝒪 G := hadj ▸ Algebra.mem_top
    induction hx using Algebra.adjoin_induction with
    | mem g hg =>
      obtain ⟨P, hP, hP0⟩ := hG g hg
      refine Module.End.isSemisimple_of_squarefree_aeval_eq_zero
        (p := P.map (Int.castRingHom K)) ?_ ?_
      · rw [← PerfectField.separable_iff_squarefree] at hP ⊢
        have := hP.map (f := algebraMap ℚ K)
        rwa [Polynomial.map_map, RingHom.eq_intCast' ((algebraMap ℚ K).comp (Int.castRingHom ℚ))]
          at this
      · have h2 : aeval (Ψ g) P = Ψ.toIntAlgHom (aeval g P) :=
          (Polynomial.aeval_algHom_apply Ψ.toIntAlgHom g P)
        rw [aeval_def, eval₂_map, RingHom.ext_int ((algebraMap K _).comp (Int.castRingHom K))
          (algebraMap ℤ _), ← aeval_def, h2, hP0, map_zero]
    | algebraMap r =>
      have : Ψ (algebraMap 𝒪 T r) = algebraMap 𝒪 K r • (1 : Module.End K (ι → K)) := by
        rw [hΨ, AlgHom.commutes, IsScalarTower.algebraMap_apply 𝒪 K (Matrix ι ι K),
          Algebra.algebraMap_eq_smul_one, map_smul, Matrix.toLin'_one, Module.End.one_eq_id]
      rw [this]
      exact Module.End.IsSemisimple_smul _ Module.End.isSemisimple_id
    | add x y _ _ hx hy => rw [map_add]; exact hx.add_of_commute (hΨc x y) hy
    | mul x y _ _ hx hy => rw [map_mul]; exact hx.mul_of_commute (hΨc x y) hy
  refine ⟨fun x hx => hΨinj ?_⟩
  rw [map_zero]
  exact Module.End.eq_zero_of_isNilpotent_isSemisimple (hx.map Ψ) (hss x)

end Part1

section Part2

variable {A : Type} [CommRing A] [IsReduced A]

theorem squarefree_map_minpoly_of_isReduced (t : A) (ht : IsIntegral ℤ t) :
    Squarefree ((minpoly ℤ t).map (Int.castRingHom ℚ)) := by
  classical
  nontriviality A
  set P := minpoly ℤ t with hPdef
  have hPm : P.Monic := minpoly.monic ht
  have hmapeq : (Int.castRingHom ℚ) = algebraMap ℤ ℚ := RingHom.eq_intCast' _ |>.symm
  rw [hmapeq]
  intro g hg
  by_contra hgu
  have hPQ0 : P.map (algebraMap ℤ ℚ) ≠ 0 := (hPm.map _).ne_zero
  have hg0 : g ≠ 0 := fun h => hPQ0 (by
    obtain ⟨s, hs⟩ := hg; rw [hs, h, zero_mul, zero_mul])

  set g₁ := g * C (leadingCoeff g)⁻¹ with hg₁
  have hg₁m : g₁.Monic := monic_mul_leadingCoeff_inv hg0
  have hg₁g : Associated g₁ g :=
    (associated_mul_isUnit_left_iff (isUnit_C.mpr
      (inv_ne_zero (leadingCoeff_ne_zero.mpr hg0)).isUnit)).mpr (Associated.refl g) |>.symm.symm
  have hdvd : g₁ * g₁ ∣ P.map (algebraMap ℤ ℚ) :=
    (Associated.dvd_iff_dvd_left (hg₁g.mul_mul hg₁g)).mpr hg
  obtain ⟨s, hs⟩ := hdvd

  obtain ⟨a, ha⟩ := IsIntegrallyClosed.eq_map_mul_C_of_dvd (K := ℚ) hPm
    (⟨g₁ * s, by rw [hs, mul_assoc]⟩ : g₁ ∣ P.map (algebraMap ℤ ℚ))
  rw [hg₁m.leadingCoeff, C_1, mul_one] at ha
  have hsm : s.Monic := by
    have := (hPm.map (algebraMap ℤ ℚ)).leadingCoeff
    rw [hs, leadingCoeff_mul, leadingCoeff_mul, hg₁m.leadingCoeff, one_mul, one_mul] at this
    exact this
  obtain ⟨c, hc⟩ := IsIntegrallyClosed.eq_map_mul_C_of_dvd (K := ℚ) hPm
    (⟨g₁ * g₁, by rw [hs, mul_comm]⟩ : s ∣ P.map (algebraMap ℤ ℚ))
  rw [hsm.leadingCoeff, C_1, mul_one] at hc
  have ham : a.Monic := monic_of_injective (algebraMap ℤ ℚ).injective_int (ha ▸ hg₁m)
  have hcm : c.Monic := monic_of_injective (algebraMap ℤ ℚ).injective_int (hc ▸ hsm)
  have hPeq : P = a * a * c := Polynomial.map_injective _ (algebraMap ℤ ℚ).injective_int (by
    rw [Polynomial.map_mul, Polynomial.map_mul, ha, hc, hs])

  have hq0 : aeval t (a * c) = 0 := by
    refine IsReduced.eq_zero _ ⟨2, ?_⟩
    rw [← map_pow, show (a * c) ^ 2 = P * c by rw [hPeq]; ring, map_mul, minpoly.aeval, zero_mul]
  have hmin := minpoly.min ℤ t (ham.mul hcm) hq0
  rw [← hPdef, hPeq, degree_mul, degree_mul, degree_mul] at hmin
  have hapos : 0 < degree a := by
    have : 0 < degree g₁ := degree_pos_of_ne_zero_of_nonunit hg₁m.ne_zero
      (fun hu => hgu (hg₁g.isUnit hu))
    rwa [← ha, degree_map_eq_of_injective (algebraMap ℤ ℚ).injective_int] at this
  have hafin : degree a ≠ ⊥ := degree_ne_bot.mpr ham.ne_zero
  have hcfin : degree c ≠ ⊥ := degree_ne_bot.mpr hcm.ne_zero
  revert hmin hapos hafin hcfin
  generalize degree a = da; generalize degree c = dc
  cases da with
  | bot => simp
  | coe da =>
    cases dc with
    | bot => simp
    | coe dc =>
      intro hmin hapos _ _
      have h1 : (0 : WithBot ℕ) < da := hapos
      norm_cast at hmin h1
      omega

end Part2

section R3

open IsLocalRing

variable {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
  [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪] [Finite (IsLocalRing.ResidueField 𝒪)]
  [CharZero 𝒪]
  {T : Type} [CommRing T] [IsReduced T] [Algebra 𝒪 T] [Module.Finite 𝒪 T] [Module.Free 𝒪 T]

theorem eq_zero_or_eq_zero_of_smul_eq_zero_of_free {x : 𝒪} {t : T} (h : x • t = 0) :
    x = 0 ∨ t = 0 := by
  by_cases hx : x = 0
  · exact Or.inl hx
  · right
    let b := Module.Free.chooseBasis 𝒪 T
    have hrepr : b.repr (x • t) = 0 := by rw [h, map_zero]
    rw [map_smul] at hrepr
    have ht : b.repr t = 0 := by
      ext i
      have hi := DFunLike.congr_fun hrepr i
      rw [Finsupp.smul_apply, smul_eq_mul] at hi
      simpa using (mul_eq_zero.mp hi).resolve_left hx
    exact b.repr.map_eq_zero_iff.mp ht

theorem algebraMap_quotient_injective_of_mem_minimalPrimes
    (P : Ideal T) (hP : P ∈ minimalPrimes T) :
    Function.Injective (algebraMap 𝒪 (T ⧸ P)) := by
  haveI : P.IsPrime := hP.1.1
  rw [injective_iff_map_eq_zero]
  intro x hx
  by_contra hx0
  have hmem : algebraMap 𝒪 T x ∈ P := by
    rw [IsScalarTower.algebraMap_apply 𝒪 T (T ⧸ P)] at hx
    exact Ideal.Quotient.eq_zero_iff_mem.mp hx
  have hnzd : algebraMap 𝒪 T x ∈ nonZeroDivisors T := by
    rw [mem_nonZeroDivisors_iff_right]
    intro t ht
    have hsmul : x • t = 0 := by rw [Algebra.smul_def, mul_comm]; exact ht
    exact (eq_zero_or_eq_zero_of_smul_eq_zero_of_free hsmul).resolve_left hx0
  exact notMem_nonZeroDivisors_of_mem_mem_minimalPrimes hmem hP hnzd

variable (𝒪) in

abbrev IntClosure (P : Ideal T) [P.IsPrime] : Type :=
  integralClosure 𝒪 (FractionRing (T ⧸ P))

section PerPrime

variable (P : Ideal T) [P.IsPrime]
  (hinj : Function.Injective (algebraMap 𝒪 (T ⧸ P)))

include hinj in

theorem moduleFinite_intClosure : Module.Finite 𝒪 (IntClosure 𝒪 P) := by
  haveI : FaithfulSMul 𝒪 (T ⧸ P) := (faithfulSMul_iff_algebraMap_injective 𝒪 (T ⧸ P)).mpr hinj
  haveI : Module.Finite 𝒪 (T ⧸ P) :=
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ 𝒪 P).toLinearMap
      (Ideal.Quotient.mkₐ_surjective 𝒪 P)
  haveI : CharZero (T ⧸ P) := charZero_of_injective_algebraMap hinj
  haveI : CharZero (FractionRing 𝒪) :=
    charZero_of_injective_algebraMap (IsFractionRing.injective 𝒪 (FractionRing 𝒪))
  haveI : Module.IsTorsionFree 𝒪 (T ⧸ P) :=
    Module.isTorsionFree_iff_faithfulSMul.mpr inferInstance
  letI : Algebra (FractionRing 𝒪) (FractionRing (T ⧸ P)) := FractionRing.liftAlgebra _ _
  haveI : IsScalarTower 𝒪 (FractionRing 𝒪) (FractionRing (T ⧸ P)) :=
    FractionRing.isScalarTower_liftAlgebra _ _
  exact IsIntegralClosure.finite 𝒪 (FractionRing 𝒪) (FractionRing (T ⧸ P)) (IntClosure 𝒪 P)

include hinj in
theorem algebraMap_intClosure_injective :
    Function.Injective (algebraMap 𝒪 (IntClosure 𝒪 P)) := by
  have h1 : Function.Injective (algebraMap 𝒪 (FractionRing (T ⧸ P))) := by
    rw [IsScalarTower.algebraMap_eq 𝒪 (T ⧸ P) (FractionRing (T ⧸ P))]
    exact (IsFractionRing.injective (T ⧸ P) (FractionRing (T ⧸ P))).comp hinj
  intro x y hxy
  apply h1
  rw [IsScalarTower.algebraMap_apply 𝒪 (IntClosure 𝒪 P) (FractionRing (T ⧸ P)),
    IsScalarTower.algebraMap_apply 𝒪 (IntClosure 𝒪 P) (FractionRing (T ⧸ P)), hxy]

include hinj in
theorem charZero_intClosure : CharZero (IntClosure 𝒪 P) :=
  charZero_of_injective_algebraMap (algebraMap_intClosure_injective P hinj)

include hinj in

theorem isDedekindDomain_intClosure : IsDedekindDomain (IntClosure 𝒪 P) := by
  haveI : FaithfulSMul 𝒪 (T ⧸ P) := (faithfulSMul_iff_algebraMap_injective 𝒪 (T ⧸ P)).mpr hinj
  haveI : Module.Finite 𝒪 (T ⧸ P) :=
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ 𝒪 P).toLinearMap
      (Ideal.Quotient.mkₐ_surjective 𝒪 P)
  haveI : CharZero (T ⧸ P) := charZero_of_injective_algebraMap hinj
  haveI : CharZero (FractionRing 𝒪) :=
    charZero_of_injective_algebraMap (IsFractionRing.injective 𝒪 (FractionRing 𝒪))
  haveI : Module.IsTorsionFree 𝒪 (T ⧸ P) :=
    Module.isTorsionFree_iff_faithfulSMul.mpr inferInstance
  letI : Algebra (FractionRing 𝒪) (FractionRing (T ⧸ P)) := FractionRing.liftAlgebra _ _
  haveI : IsScalarTower 𝒪 (FractionRing 𝒪) (FractionRing (T ⧸ P)) :=
    FractionRing.isScalarTower_liftAlgebra _ _
  exact IsIntegralClosure.isDedekindDomain 𝒪 (FractionRing 𝒪) (FractionRing (T ⧸ P))
    (IntClosure 𝒪 P)

include hinj in
theorem isDVR_intClosure [IsLocalRing (IntClosure 𝒪 P)] :
    IsDiscreteValuationRing (IntClosure 𝒪 P) := by
  haveI : IsDedekindDomain (IntClosure 𝒪 P) := isDedekindDomain_intClosure P hinj
  refine ⟨?_⟩
  intro hbot
  have hfieldR : IsField (IntClosure 𝒪 P) := IsLocalRing.isField_iff_maximalIdeal_eq.mpr hbot
  have hfield𝒪 : IsField 𝒪 :=
    isField_of_isIntegral_of_isField (algebraMap_intClosure_injective P hinj) hfieldR
  exact IsDiscreteValuationRing.not_a_field 𝒪 (IsLocalRing.isField_iff_maximalIdeal_eq.mp hfield𝒪)

include hinj in
theorem isLocalHom_intClosure [IsLocalRing (IntClosure 𝒪 P)] :
    IsLocalHom (algebraMap 𝒪 (IntClosure 𝒪 P)) := by
  haveI : FaithfulSMul 𝒪 (IntClosure 𝒪 P) :=
    (faithfulSMul_iff_algebraMap_injective 𝒪 (IntClosure 𝒪 P)).mpr
      (algebraMap_intClosure_injective P hinj)
  exact Algebra.IsIntegral.isLocalHom 𝒪 (IntClosure 𝒪 P)

include hinj in

theorem isAdicComplete_intClosure [IsLocalRing (IntClosure 𝒪 P)] :
    IsAdicComplete (IsLocalRing.maximalIdeal (IntClosure 𝒪 P)) (IntClosure 𝒪 P) := by
  haveI := moduleFinite_intClosure P hinj
  haveI := isLocalHom_intClosure P hinj
  exact IsLocalRing.isAdicComplete_of_module_finite (𝒪 := 𝒪)

include hinj in

theorem finite_residueField_intClosure [IsLocalRing (IntClosure 𝒪 P)] :
    Finite (IsLocalRing.ResidueField (IntClosure 𝒪 P)) := by
  haveI := moduleFinite_intClosure P hinj
  haveI := isLocalHom_intClosure P hinj
  exact IsLocalRing.ResidueField.finite_of_finite (R := 𝒪) ‹_›

noncomputable def toIntClosure : T →ₐ[𝒪] IntClosure 𝒪 P :=
  AlgHom.codRestrict
    ((IsScalarTower.toAlgHom 𝒪 (T ⧸ P) (FractionRing (T ⧸ P))).comp (Ideal.Quotient.mkₐ 𝒪 P))
    (integralClosure 𝒪 (FractionRing (T ⧸ P)))
    (fun t => (Algebra.IsIntegral.isIntegral (R := 𝒪) t).map
      ((IsScalarTower.toAlgHom 𝒪 (T ⧸ P) (FractionRing (T ⧸ P))).comp (Ideal.Quotient.mkₐ 𝒪 P)))

theorem toIntClosure_eq_zero_iff {t : T} :
    toIntClosure (𝒪 := 𝒪) P t = 0 ↔ t ∈ P := by
  constructor
  · intro h
    have hval : algebraMap (T ⧸ P) (FractionRing (T ⧸ P)) (Ideal.Quotient.mk P t) = 0 := by
      have := congrArg (Subtype.val) h
      simpa [toIntClosure] using this
    have hmk : Ideal.Quotient.mk P t = 0 :=
      (map_eq_zero_iff _ (IsFractionRing.injective (T ⧸ P) (FractionRing (T ⧸ P)))).mp hval
    exact Ideal.Quotient.eq_zero_iff_mem.mp hmk
  · intro h
    apply Subtype.ext
    show algebraMap (T ⧸ P) (FractionRing (T ⧸ P)) (Ideal.Quotient.mk P t) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr h, map_zero]

end PerPrime

theorem exists_embedding_into_dvrs_finite_of_local
    (hloc : ∀ (D : Type) [CommRing D] [IsDomain D] [Algebra 𝒪 D] [Module.Finite 𝒪 D],
      IsLocalRing D) :
    ∃ (n : ℕ) (R : Fin n → Type) (_ : ∀ j, CommRing (R j)) (_ : ∀ j, IsDomain (R j))
      (_ : ∀ j, IsDiscreteValuationRing (R j))
      (_ : ∀ j, IsAdicComplete (IsLocalRing.maximalIdeal (R j)) (R j))
      (_ : ∀ j, Finite (IsLocalRing.ResidueField (R j))) (_ : ∀ j, CharZero (R j))
      (_ : ∀ j, Algebra 𝒪 (R j)) (_ : ∀ j, Module.Finite 𝒪 (R j))
      (_ : ∀ j, IsLocalHom (algebraMap 𝒪 (R j)))
      (ι : T →ₐ[𝒪] ((j : Fin n) → R j)),
      Function.Injective ι := by
  haveI : IsNoetherianRing T := Algebra.FiniteType.isNoetherianRing 𝒪 T
  have hfin : (minimalPrimes T).Finite := minimalPrimes.finite_of_isNoetherianRing T
  haveI := hfin.fintype
  let e : Fin (Fintype.card (minimalPrimes T)) ≃ (minimalPrimes T) := (Fintype.equivFin _).symm
  haveI hprime : ∀ j, ((e j : Ideal T)).IsPrime := fun j => (e j).2.1.1
  have hinj : ∀ j, Function.Injective (algebraMap 𝒪 (T ⧸ (e j : Ideal T))) := fun j =>
    algebraMap_quotient_injective_of_mem_minimalPrimes _ (e j).2
  haveI hlocal : ∀ j, IsLocalRing (IntClosure 𝒪 (e j : Ideal T)) := fun j => by
    haveI := moduleFinite_intClosure (𝒪 := 𝒪) (e j : Ideal T) (hinj j)
    exact hloc _
  refine ⟨_, fun j => IntClosure 𝒪 (e j : Ideal T),
    fun j => inferInstance,
    fun j => inferInstance,
    fun j => isDVR_intClosure _ (hinj j),
    fun j => isAdicComplete_intClosure _ (hinj j),
    fun j => finite_residueField_intClosure _ (hinj j),
    fun j => charZero_intClosure _ (hinj j),
    fun j => inferInstance,
    fun j => moduleFinite_intClosure _ (hinj j),
    fun j => isLocalHom_intClosure _ (hinj j),
    Pi.algHom _ _ (fun j => toIntClosure (e j : Ideal T)),
    ?_⟩
  rw [injective_iff_map_eq_zero]
  intro t ht
  have hmem : ∀ p ∈ minimalPrimes T, t ∈ p := by
    intro p hp
    have hj := congr_fun ht (e.symm ⟨p, hp⟩)
    have hzero : toIntClosure (𝒪 := 𝒪) (e (e.symm ⟨p, hp⟩) : Ideal T) t = 0 := hj
    have hP : t ∈ (e (e.symm ⟨p, hp⟩) : Ideal T) :=
      (toIntClosure_eq_zero_iff _).mp hzero
    have : (e (e.symm ⟨p, hp⟩) : Ideal T) = p := by rw [e.apply_symm_apply]
    exact this ▸ hP
  have hsinf : t ∈ sInf ((⊥ : Ideal T).minimalPrimes) :=
    Submodule.mem_sInf.mpr (fun p hp => hmem p hp)
  rw [Ideal.sInf_minimalPrimes, ← Ideal.zero_eq_bot, ← nilradical, nilradical_eq_zero,
    Ideal.zero_eq_bot] at hsinf
  exact (Ideal.mem_bot).mp hsinf

theorem exists_embedding_into_dvrs_of_local
    (hloc : ∀ (D : Type) [CommRing D] [IsDomain D] [Algebra 𝒪 D] [Module.Finite 𝒪 D],
      IsLocalRing D) :
    ∃ (n : ℕ) (R : Fin n → Type) (_ : ∀ j, CommRing (R j)) (_ : ∀ j, IsDomain (R j))
      (_ : ∀ j, IsDiscreteValuationRing (R j))
      (_ : ∀ j, IsAdicComplete (IsLocalRing.maximalIdeal (R j)) (R j))
      (_ : ∀ j, Finite (IsLocalRing.ResidueField (R j))) (_ : ∀ j, CharZero (R j))
      (_ : ∀ j, Algebra 𝒪 (R j)) (_ : ∀ j, IsLocalHom (algebraMap 𝒪 (R j)))
      (ι : T →ₐ[𝒪] ((j : Fin n) → R j)),
      Function.Injective ι := by
  obtain ⟨n, R, h1, h2, h3, h4, h5, h6, h7, _, h9, ι, hι⟩ :=
    exists_embedding_into_dvrs_finite_of_local (T := T) hloc
  exact ⟨n, R, h1, h2, h3, h4, h5, h6, h7, h9, ι, hι⟩

theorem exists_embedding_into_dvrs_of_local' [Nontrivial T]
    (hloc : ∀ (D : Type) [CommRing D] [IsDomain D] [Algebra 𝒪 D] [Module.Finite 𝒪 D],
      IsLocalRing D) :
    ∃ (n : ℕ) (_ : NeZero n) (R : Fin n → Type) (_ : ∀ j, CommRing (R j))
      (_ : ∀ j, IsDomain (R j)) (_ : ∀ j, IsDiscreteValuationRing (R j))
      (_ : ∀ j, IsAdicComplete (IsLocalRing.maximalIdeal (R j)) (R j))
      (_ : ∀ j, Finite (IsLocalRing.ResidueField (R j))) (_ : ∀ j, CharZero (R j))
      (_ : ∀ j, Algebra 𝒪 (R j)) (_ : ∀ j, Module.Finite 𝒪 (R j))
      (_ : ∀ j, IsLocalHom (algebraMap 𝒪 (R j)))
      (ι : T →ₐ[𝒪] ((j : Fin n) → R j)),
      Function.Injective ι := by
  obtain ⟨n, R, h1, h2, h3, h4, h5, h6, h7, h8, h9, ι, hι⟩ :=
    exists_embedding_into_dvrs_finite_of_local (T := T) hloc
  have hn : n ≠ 0 := by
    rintro rfl
    have h10 : ι 1 = ι 0 := funext fun j => j.elim0
    exact one_ne_zero (hι h10)
  exact ⟨n, ⟨hn⟩, R, h1, h2, h3, h4, h5, h6, h7, h8, h9, ι, hι⟩

theorem exists_embedding_into_dvrs :
    ∃ (n : ℕ) (R : Fin n → Type) (_ : ∀ j, CommRing (R j)) (_ : ∀ j, IsDomain (R j))
      (_ : ∀ j, IsDiscreteValuationRing (R j))
      (_ : ∀ j, IsAdicComplete (IsLocalRing.maximalIdeal (R j)) (R j))
      (_ : ∀ j, Finite (IsLocalRing.ResidueField (R j))) (_ : ∀ j, CharZero (R j))
      (_ : ∀ j, Algebra 𝒪 (R j)) (_ : ∀ j, IsLocalHom (algebraMap 𝒪 (R j)))
      (ι : T →ₐ[𝒪] ((j : Fin n) → R j)),
      Function.Injective ι :=
  exists_embedding_into_dvrs_of_local
    (fun D _ _ _ _ => IsLocalRing.of_isDomain_of_moduleFinite_of_isAdicComplete 𝒪 D)

end R3

section LocalHom

open IsLocalRing

variable {𝒪 : Type} [CommRing 𝒪] [IsLocalRing 𝒪]
  {T : Type} [CommRing T] [IsLocalRing T] [Algebra 𝒪 T] [Module.Finite 𝒪 T]

theorem isLocalHom_of_algHom {R' : Type} [CommRing R'] [IsLocalRing R'] [Algebra 𝒪 R']
    [IsLocalHom (algebraMap 𝒪 R')] (f : T →ₐ[𝒪] R') : IsLocalHom f.toRingHom := by
  have hP : ((maximalIdeal R').comap f.toRingHom).IsPrime := Ideal.comap_isPrime _ _
  have hc : ((maximalIdeal R').comap f.toRingHom).comap (algebraMap 𝒪 T) = maximalIdeal 𝒪 := by
    rw [Ideal.comap_comap]
    have : f.toRingHom.comp (algebraMap 𝒪 T) = algebraMap 𝒪 R' := f.comp_algebraMap
    rw [this]
    exact maximalIdeal_comap _
  have hM : ((maximalIdeal R').comap f.toRingHom).IsMaximal := by
    refine Ideal.isMaximal_of_isIntegral_of_isMaximal_comap (R := 𝒪) _ ?_
    rw [hc]
    infer_instance
  have heq : (maximalIdeal R').comap f.toRingHom = maximalIdeal T := eq_maximalIdeal hM
  exact ((local_hom_TFAE f.toRingHom).out 4 0).mp heq

end LocalHom

section Reduced

theorem isReduced_carrier (N : ℕ) [NeZero N] (S : Set ℕ) (hNS : ∀ q : ℕ, q.Prime → q ∣ N → q ∈ S)
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [CharZero 𝒪]
    {T : Type} [CommRing T] [Algebra 𝒪 T] [Module.Free 𝒪 T] [Module.Finite 𝒪 T]
    (π : CuspForm.heckeAlgebra N 2 S →+* T) (hadj : Algebra.adjoin 𝒪 (Set.range π) = ⊤) :
    IsReduced T := by
  haveI := CuspForm.isReduced_heckeAlgebra_of_primeFactors_subset N S hNS
  haveI := CuspForm.moduleFinite_heckeAlgebra_two N S
  refine isReduced_of_free_of_adjoin_eq_top (Set.range π) hadj ?_
  rintro _ ⟨t, rfl⟩
  have ht : IsIntegral ℤ t := Algebra.IsIntegral.isIntegral _
  refine ⟨minpoly ℤ t, squarefree_map_minpoly_of_isReduced t ht, ?_⟩
  have h := Polynomial.aeval_algHom_apply π.toIntAlgHom t (minpoly ℤ t)
  rw [minpoly.aeval, map_zero] at h
  exact h

end Reduced

end K6Points

open IsLocalRing in
theorem solution {N : ℕ} [NeZero N] {S : Finset ℕ}
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪]
    {θ : CuspForm.heckeAlgebra N 2 (↑S : Set ℕ) →+* IsLocalRing.ResidueField 𝒪}
    {T : Type} [CommRing T] [IsLocalRing T] [IsNoetherianRing T]
    [IsAdicComplete (IsLocalRing.maximalIdeal T) T] [Algebra 𝒪 T] [IsLocalHom (algebraMap 𝒪 T)]
    [Module.Finite 𝒪 T] [Module.Free 𝒪 T]
    [Finite (IsLocalRing.ResidueField 𝒪)] [CharZero 𝒪]
    (hNS : ∀ q : ℕ, q.Prime → q ∣ N → q ∈ S)
    (H : CuspForm.HeckeGaloisRepDatum N (↑S : Set ℕ) 𝒪 θ T) :
    ∃ (n : ℕ) (A : Fin n → Type) (_ : ∀ i, CommRing (A i)) (_ : ∀ i, IsDomain (A i))
      (_ : ∀ i, IsDiscreteValuationRing (A i))
      (_ : ∀ i, IsAdicComplete (IsLocalRing.maximalIdeal (A i)) (A i))
      (_ : ∀ i, Finite (IsLocalRing.ResidueField (A i))) (_ : ∀ i, CharZero (A i))
      (_ : ∀ i, Algebra 𝒪 (A i)) (_ : ∀ i, Module.Finite 𝒪 (A i))
      (_ : ∀ i, IsLocalHom (algebraMap 𝒪 (A i)))
      (χ : ∀ i, T →ₐ[𝒪] A i),
      (∀ i, IsLocalHom (χ i).toRingHom) ∧ (∀ x : T, (∀ i, χ i x = 0) → x = 0) := by
  haveI : IsReduced T :=
    K6Points.isReduced_carrier N (↑S : Set ℕ) (fun q hq hqN => Finset.mem_coe.mpr (hNS q hq hqN))
      H.π H.adjoin_range_π
  obtain ⟨n, R, h1, h2, h3, h4, h5, h6, h7, h8, h9, ι, hι⟩ :=
    K6Points.exists_embedding_into_dvrs_finite_of_local (𝒪 := 𝒪) (T := T)
      (fun D _ _ _ _ => IsLocalRing.of_isDomain_of_moduleFinite_of_isAdicComplete 𝒪 D)
  refine ⟨n, R, h1, h2, h3, h4, h5, h6, h7, h8, h9,
    fun i => (Pi.evalAlgHom 𝒪 (fun j => R j) i).comp ι, fun i => ?_, fun x hx => ?_⟩
  · exact K6Points.isLocalHom_of_algHom _
  · apply hι
    rw [map_zero]
    funext i
    exact hx i

end S_CuspForm_HeckeGaloisRepDatum_exists_points_jointly_injective
end P2MW
export P2MW.S_CuspForm_HeckeGaloisRepDatum_exists_points_jointly_injective (solution)
