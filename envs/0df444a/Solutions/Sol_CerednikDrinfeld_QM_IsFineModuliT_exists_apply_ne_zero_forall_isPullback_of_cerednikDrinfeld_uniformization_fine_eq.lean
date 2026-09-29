-- Prove2me | solution 1 for CerednikDrinfeld.QM.IsFineModuliT.exists_apply_ne_zero_forall_isPullback_of_cerednikDrinfeld_uniformization_fine_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/1c8dd345-361d-55c5-acfe-56aa9ef1e1e5

import Mathlib
import Definitions.Def_CerednikDrinfeld_QMCoarseModuli
import Definitions.Def_CerednikDrinfeld_QMFineModuli
import Definitions.Def_CerednikDrinfeld_QMFineModuliT
import Definitions.Def_CerednikDrinfeld_AlgFunctorConst
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneFunctor
import Definitions.Def_CerednikDrinfeld_SchemeNilpPoints
import Definitions.Def_CerednikDrinfeld_CosetGraphAtPrime
import Definitions.Def_CerednikDrinfeld_HeckeTower
import Definitions.Def_CerednikDrinfeld_ClassSetGraph
import Theorems.Thm_CerednikDrinfeld_QM_IsFineModuliT_cerednikDrinfeld_uniformization_fine_eq_of_forall_frobFixed_eq
import Theorems.Thm_CerednikDrinfeld_FormalOmega_DeligneDatum_exists_finset_forall_map_eq_iff_of_map_eq
import Theorems.Thm_CerednikDrinfeld_CosetGraph_padicValRat_nrd_eq_zero_of_mem_awayUnits
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_IsFineModuliT_exists_apply_ne_zero_forall_isPullback_of_cerednikDrinfeld_uniformization_fine_eq
p2m_attr_erase "instance" "CerednikDrinfeld.Omega.HolRingOf.instSMulCommClass CerednikDrinfeld.Omega.holRingAction CerednikDrinfeld.Omega.holRingSMulCommClass CerednikDrinfeld.Omega.HolRingOf.instAlgebra CerednikDrinfeld.Omega.HolRingOf.instCommRing CerednikDrinfeld.Omega.HolRingOf.instMulSemiringAction CerednikDrinfeld.Omega.holRingAlgebra CerednikDrinfeld.Omega.IsometricAut.instGroup CerednikDrinfeld.Omega.pglOmegaAction CerednikDrinfeld.Mumford.AmbientSemilinearAut.instGroup CerednikDrinfeld.Mumford.invariantFieldAlgebra CerednikDrinfeld.Mumford.invariantFieldOfAlgebra"
p2m_attr_erase "simp" "CerednikDrinfeld.Mumford.vertexType_self CerednikDrinfeld.Mumford.mem_typePreserving_iff"

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory AlgebraicGeometry QuaternionAlgebra IsDedekindDomain CerednikDrinfeld CerednikDrinfeld.QM CerednikDrinfeld.FormalOmega NeronModelInfra

noncomputable section

namespace Q2SpreadT

p2m_open "Polynomial AlgebraicGeometry.Polynomial"

section Roots

variable {B : Type} [CommRing B]

theorem exists_pow_sub_expand (q : ℕ) (a b : B) :
    ∃ k : B, b ^ q - b = (a ^ q - a) + ((q : B) * a ^ (q - 1) - 1) * (b - a) + k * (b - a) ^ 2 := by
  obtain ⟨k, hk⟩ := Polynomial.binomExpansion ((X : B[X]) ^ q - X) a (b - a)
  refine ⟨k, ?_⟩
  have hab : a + (b - a) = b := by ring
  rw [hab] at hk
  simp only [eval_sub, eval_pow, eval_X, derivative_sub, derivative_X_pow, derivative_X, eval_mul, eval_one,
    map_natCast, eval_natCast] at hk
  rw [hk]

theorem exists_mul_eq_zero_of_pow_eq (q : ℕ) (a b : B) (ha : a ^ q = a) (hb : b ^ q = b) :
    ∃ f : B, (b - a) * f = 0 ∧ ∃ k : B, f = ((q : B) * a ^ (q - 1) - 1) + k * (b - a) := by
  obtain ⟨k, hk⟩ := exists_pow_sub_expand q a b
  refine ⟨((q : B) * a ^ (q - 1) - 1) + k * (b - a), ?_, k, rfl⟩
  have h0 : (a ^ q - a) = 0 := by rw [ha, sub_self]
  have h1 : b ^ q - b = 0 := by rw [hb, sub_self]
  rw [h0, h1, zero_add] at hk
  have : (b - a) * ((q : B) * a ^ (q - 1) - 1 + k * (b - a)) =
      ((q : B) * a ^ (q - 1) - 1) * (b - a) + k * (b - a) ^ 2 := by ring
  rw [this, ← hk]

theorem isUnit_deriv_of_isNilpotent (q : ℕ) (hq : IsNilpotent (q : B)) (a : B) :
    IsUnit ((q : B) * a ^ (q - 1) - 1) := by
  have h : IsNilpotent ((q : B) * a ^ (q - 1)) := Commute.isNilpotent_mul_right (Commute.all _ _) hq
  have := (h.neg).isUnit_add_one
  have e : (q : B) * a ^ (q - 1) - 1 = -(-((q : B) * a ^ (q - 1)) + 1) := by ring
  rw [e]
  exact this.neg

theorem exists_spread_of_pow_eq (q : ℕ) (hq : IsNilpotent (q : B)) (a b : B) (ha : a ^ q = a) (hb : b ^ q = b) :
    ∃ f : B, (∀ {C : Type} [CommRing C] (χ : B →+* C), IsUnit (χ f) → χ a = χ b) ∧
      ∀ {L : Type} [CommRing L] (φ : B →+* L), φ a = φ b → IsUnit (φ f) := by
  obtain ⟨f, hf, k, hk⟩ := exists_mul_eq_zero_of_pow_eq q a b ha hb
  refine ⟨f, fun χ hχ => ?_, fun φ hφ => ?_⟩
  · have := congrArg χ hf
    rw [map_mul, map_zero] at this
    have h2 : χ (b - a) = 0 := (hχ.mul_left_eq_zero).mp this
    rw [map_sub, sub_eq_zero] at h2
    exact h2.symm
  · rw [hk, map_add, map_mul, map_sub φ b, hφ, sub_self, mul_zero, add_zero]
    exact (isUnit_deriv_of_isNilpotent q hq a).map φ

end Roots

section Teichmuller

variable {R : Type} [CommRing R]

theorem eq_of_pow_eq_of_sub_mem (I : Ideal R) (hI : I ≤ Ideal.jacobson ⊥) (q : ℕ) (hq : (q : R) ∈ I)
    (a b : R) (ha : a ^ q = a) (hb : b ^ q = b) (hab : b - a ∈ I) : a = b := by
  obtain ⟨f, hf, k, hk⟩ := exists_mul_eq_zero_of_pow_eq q a b ha hb
  have hfI : f + 1 ∈ I := by
    rw [hk]
    have : (q : R) * a ^ (q - 1) - 1 + k * (b - a) + 1 = (q : R) * a ^ (q - 1) + k * (b - a) := by ring
    rw [this]
    exact I.add_mem (I.mul_mem_right _ hq) (I.mul_mem_left _ hab)
  have hu : IsUnit f := by
    have hmem : f + 1 ∈ Ideal.jacobson (⊥ : Ideal R) := hI hfI
    have := Ideal.mem_jacobson_bot.mp hmem
    have h := this (-1)
    have e : (f + 1) * (-1 : R) + 1 = -f := by ring
    rw [e] at h
    simpa using h.neg
  have h2 : b - a = 0 := (hu.mul_left_eq_zero).mp hf
  exact (sub_eq_zero.mp h2).symm

theorem exists_teichmuller (I : Ideal R) [HenselianRing R I] (q : ℕ) (hq2 : 2 ≤ q) (hq : (q : R) ∈ I)
    (y : R) (hy : y ^ q - y ∈ I) : ∃ t : R, t ^ q = t ∧ t - y ∈ I := by
  nontriviality R
  have hmonic : ((X : R[X]) ^ q - X).Monic := by
    apply Polynomial.monic_X_pow_sub
    rw [degree_X]
    exact_mod_cast hq2
  have heval : ((X : R[X]) ^ q - X).eval y ∈ I := by
    simpa only [eval_sub, eval_pow, eval_X] using hy
  have hder : IsUnit (Ideal.Quotient.mk I (((X : R[X]) ^ q - X).derivative.eval y)) := by
    have e : ((X : R[X]) ^ q - X).derivative.eval y = (q : R) * y ^ (q - 1) - 1 := by
      simp only [derivative_sub, derivative_X_pow, derivative_X, eval_sub, eval_mul, eval_pow, eval_X, eval_one,
        map_natCast, eval_natCast]
    rw [e]
    have hq0 : Ideal.Quotient.mk I ((q : R) * y ^ (q - 1)) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (I.mul_mem_right _ hq)
    rw [map_sub, hq0, map_one, zero_sub]
    exact isUnit_one.neg
  obtain ⟨t, ht, hty⟩ := HenselianRing.is_henselian _ hmonic y heval hder
  refine ⟨t, ?_, hty⟩
  have := ht
  rw [IsRoot.def, eval_sub, eval_pow, eval_X] at this
  exact sub_eq_zero.mp this

end Teichmuller

section Digits

variable {𝒪 : Type} [CommRing 𝒪] {Onr : Type} [CommRing Onr] [Algebra 𝒪 Onr]

theorem map_mem_span (π : 𝒪) (σ : Onr ≃ₐ[𝒪] Onr) (x : Onr) (hx : x ∈ Ideal.span {algebraMap 𝒪 Onr π}) :
    σ x ∈ Ideal.span {algebraMap 𝒪 Onr π} := by
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hx
  rw [map_mul, AlgEquiv.commutes]
  exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)

variable (π : 𝒪) (Fam : Set (Onr ≃ₐ[𝒪] Onr)) (q : ℕ)

def Fix : Set Onr := {y | ∀ σ ∈ Fam, σ y = y}

variable {π Fam q}

theorem teich_mem_fix (hjac : Ideal.span {algebraMap 𝒪 Onr π} ≤ Ideal.jacobson ⊥)
    (hq : (q : Onr) ∈ Ideal.span {algebraMap 𝒪 Onr π}) (t y : Onr) (ht : t ^ q = t) (hy : y ∈ Fix Fam)
    (hty : t - y ∈ Ideal.span {algebraMap 𝒪 Onr π}) : t ∈ Fix Fam := by
  intro σ hσ
  symm
  apply eq_of_pow_eq_of_sub_mem _ hjac q hq t (σ t) ht (by rw [← map_pow, ht])
  have : σ t - t = σ (t - y) - (t - y) := by rw [map_sub, hy σ hσ]; ring
  rw [this]
  exact Ideal.sub_mem _ (map_mem_span π σ _ hty) hty

theorem quot_mem_fix [IsDomain Onr] (hπ0 : algebraMap 𝒪 Onr π ≠ 0) (y t y' : Onr) (hy : y ∈ Fix Fam) (ht : t ∈ Fix Fam)
    (h : y' * algebraMap 𝒪 Onr π = y - t) : y' ∈ Fix Fam := by
  intro σ hσ
  have := congrArg σ h
  rw [map_mul, AlgEquiv.commutes, map_sub, hy σ hσ, ht σ hσ, ← h] at this
  exact mul_right_cancel₀ hπ0 this

theorem exists_digits [IsDomain Onr] (hcomplete : IsAdicComplete (Ideal.span {algebraMap 𝒪 Onr π}) Onr)
    (hq2 : 2 ≤ q) (hq : (q : Onr) ∈ Ideal.span {algebraMap 𝒪 Onr π}) (hπ0 : algebraMap 𝒪 Onr π ≠ 0)
    (σ₀ : Onr ≃ₐ[𝒪] Onr) (hσ₀ : σ₀ ∈ Fam) (hσ₀q : ∀ y : Onr, σ₀ y - y ^ q ∈ Ideal.span {algebraMap 𝒪 Onr π})
    (e : ℕ) : ∀ y : Onr, y ∈ Fix Fam → ∃ (ts : Fin e → Onr) (y' : Onr),
      (∀ j, ts j ^ q = ts j ∧ ts j ∈ Fix Fam) ∧ y = (∑ j, ts j * algebraMap 𝒪 Onr π ^ (j : ℕ)) + algebraMap 𝒪 Onr π ^ e * y' := by
  haveI := hcomplete
  haveI : HenselianRing Onr (Ideal.span {algebraMap 𝒪 Onr π}) := IsAdicComplete.henselianRing Onr _
  have hjac : Ideal.span {algebraMap 𝒪 Onr π} ≤ Ideal.jacobson ⊥ := IsAdicComplete.le_jacobson_bot _
  induction e with
  | zero =>
    intro y hy
    refine ⟨fun j => j.elim0, y, fun j => j.elim0, ?_⟩
    rw [Finset.univ_eq_empty, Finset.sum_empty, zero_add, pow_zero, one_mul]
  | succ e ih =>
    intro y hy
    have hyq : y ^ q - y ∈ Ideal.span {algebraMap 𝒪 Onr π} := by
      have h1 := hσ₀q y
      rw [hy σ₀ hσ₀] at h1
      have : y ^ q - y = -(y - y ^ q) := by ring
      rw [this]
      exact neg_mem h1
    obtain ⟨t, ht, hty⟩ := exists_teichmuller _ q hq2 hq y hyq
    have htS : t ∈ Fix Fam := teich_mem_fix hjac hq t y ht hy hty
    have hyt : y - t ∈ Ideal.span {algebraMap 𝒪 Onr π} := by
      have : y - t = -(t - y) := by ring
      rw [this]; exact neg_mem hty
    obtain ⟨y₁, hy₁⟩ := Ideal.mem_span_singleton'.mp hyt
    have hy₁S : y₁ ∈ Fix Fam := quot_mem_fix hπ0 y t y₁ hy htS hy₁
    obtain ⟨ts, y', hts, hy₁eq⟩ := ih y₁ hy₁S
    refine ⟨Fin.cons t ts, y', ?_, ?_⟩
    · intro j
      refine Fin.cases ?_ (fun i => ?_) j
      · simp only [Fin.cons_zero]; exact ⟨ht, htS⟩
      · simp only [Fin.cons_succ]; exact hts i
    · rw [Fin.sum_univ_succ]
      simp only [Fin.cons_zero, Fin.cons_succ, Fin.val_zero, pow_zero, mul_one, Fin.val_succ]
      have hy' : y = t + algebraMap 𝒪 Onr π * y₁ := by rw [mul_comm, hy₁]; ring
      have hsum : ∑ j : Fin e, ts j * algebraMap 𝒪 Onr π ^ ((j : ℕ) + 1) =
          algebraMap 𝒪 Onr π * ∑ j : Fin e, ts j * algebraMap 𝒪 Onr π ^ (j : ℕ) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        rw [pow_succ]; ring
      rw [hsum, hy', hy₁eq, pow_succ]; ring

theorem apply_digits {B : Type} [CommRing B] [Algebra 𝒪 B] {C : Type} [CommRing C] [Algebra 𝒪 C]
    (ψ : Onr →ₐ[𝒪] B) (χ : B →ₐ[𝒪] C) {e : ℕ} (he : algebraMap 𝒪 B π ^ e = 0) (ts : Fin e → Onr) (y' : Onr) :
    χ (ψ ((∑ j, ts j * algebraMap 𝒪 Onr π ^ (j : ℕ)) + algebraMap 𝒪 Onr π ^ e * y')) =
      ∑ j, χ (ψ (ts j)) * algebraMap 𝒪 C π ^ (j : ℕ) := by
  rw [map_add, map_mul, map_pow, AlgHom.commutes, he, zero_mul, add_zero, map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [map_mul, map_pow, AlgHom.commutes, map_mul, map_pow, AlgHom.commutes]

theorem coeff_spread [IsDomain Onr] (hcomplete : IsAdicComplete (Ideal.span {algebraMap 𝒪 Onr π}) Onr)
    (hq2 : 2 ≤ q) (hq : (q : Onr) ∈ Ideal.span {algebraMap 𝒪 Onr π}) (hπ0 : algebraMap 𝒪 Onr π ≠ 0)
    (σ₀ : Onr ≃ₐ[𝒪] Onr) (hσ₀ : σ₀ ∈ Fam) (hσ₀q : ∀ y : Onr, σ₀ y - y ^ q ∈ Ideal.span {algebraMap 𝒪 Onr π})
    {B : Type} [CommRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π)) (hqB : IsNilpotent ((q : ℕ) : B))
    (ψ₁ ψ₂ : Onr →ₐ[𝒪] B) {L : Type} [Field L] [Algebra 𝒪 L] (φ : B →ₐ[𝒪] L)
    (hφ : ∀ y ∈ Fix Fam, φ (ψ₁ y) = φ (ψ₂ y)) :
    ∃ f₀ : B, φ f₀ ≠ 0 ∧ ∀ (C : Type) [CommRing C] [Algebra 𝒪 C] (χ : B →ₐ[𝒪] C), IsUnit (χ f₀) →
      ∀ y ∈ Fix Fam, χ (ψ₁ y) = χ (ψ₂ y) := by
  classical

  have hX : ((X : Onr[X]) ^ q - X) ≠ 0 := by
    apply Polynomial.Monic.ne_zero
    apply Polynomial.monic_X_pow_sub
    rw [degree_X]
    exact_mod_cast hq2
  set T₀ : Finset Onr := ((X : Onr[X]) ^ q - X).roots.toFinset with hT₀
  have hmemT₀ : ∀ t : Onr, t ^ q = t → t ∈ T₀ := by
    intro t ht
    rw [hT₀, Multiset.mem_toFinset, mem_roots hX, IsRoot.def, eval_sub, eval_pow, eval_X, ht, sub_self]

  have hex : ∀ t : Onr, ∃ ft : B,
      (t ^ q = t → ∀ (C : Type) [CommRing C] [Algebra 𝒪 C] (χ : B →ₐ[𝒪] C), IsUnit (χ ft) → χ (ψ₁ t) = χ (ψ₂ t)) ∧
      (t ^ q = t → t ∈ Fix Fam → IsUnit (φ ft)) := by
    intro t
    by_cases ht : t ^ q = t
    · have ha : ψ₁ t ^ q = ψ₁ t := by rw [← map_pow, ht]
      have hb : ψ₂ t ^ q = ψ₂ t := by rw [← map_pow, ht]
      obtain ⟨ft, h1, h2⟩ := exists_spread_of_pow_eq q hqB (ψ₁ t) (ψ₂ t) ha hb
      refine ⟨ft, fun _ C _ _ χ hχ => h1 (χ : B →+* C) hχ, fun _ htS => h2 (φ : B →+* L) (hφ t htS)⟩
    · exact ⟨1, fun h => (ht h).elim, fun h => (ht h).elim⟩
  choose ft hft₁ hft₂ using hex
  set T₁ : Finset Onr := T₀.filter (fun t => t ∈ Fix Fam) with hT₁
  refine ⟨∏ t ∈ T₁, ft t, ?_, ?_⟩
  · rw [map_prod, Finset.prod_ne_zero_iff]
    intro t ht
    rw [hT₁, Finset.mem_filter] at ht
    have htq : t ^ q = t := by
      have := ht.1
      rw [hT₀, Multiset.mem_toFinset, mem_roots hX, IsRoot.def, eval_sub, eval_pow, eval_X, sub_eq_zero] at this
      exact this
    exact (hft₂ t htq ht.2).ne_zero
  · intro C _ _ χ hχ y hy
    rw [map_prod, IsUnit.prod_iff] at hχ
    obtain ⟨e, he⟩ := hB
    obtain ⟨ts, y', hts, hyeq⟩ := exists_digits hcomplete hq2 hq hπ0 σ₀ hσ₀ hσ₀q e y hy
    rw [hyeq, apply_digits ψ₁ χ he, apply_digits ψ₂ χ he]
    apply Finset.sum_congr rfl
    intro j _
    congr 1
    have hj := hts j
    exact hft₁ (ts j) hj.1 C χ (hχ (ts j) (by rw [hT₁, Finset.mem_filter]; exact ⟨hmemT₀ _ hj.1, hj.2⟩))

end Digits

section Core

variable {𝒪 : Type} [CommRing 𝒪] {K₀ : Type} [Field K₀] [Algebra 𝒪 K₀]

theorem isUnit_powers {B : Type} [CommRing B] [Algebra 𝒪 B] {C : Type} [CommRing C] [Algebra 𝒪 C] (χ : B →ₐ[𝒪] C)
    (f : B) (hf : IsUnit (χ f)) (y : ↥(Submonoid.powers f)) : IsUnit (χ (y : B)) := by
  obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff _ _).mp y.2
  rw [← hn, map_pow]
  exact hf.pow n

def liftAway {B : Type} [CommRing B] [Algebra 𝒪 B] {C : Type} [CommRing C] [Algebra 𝒪 C] (χ : B →ₐ[𝒪] C) (f : B)
    (hf : IsUnit (χ f)) : Localization.Away f →ₐ[𝒪] C :=
  IsLocalization.liftAlgHom (M := Submonoid.powers f) (f := χ) (isUnit_powers χ f hf)

theorem liftAway_apply {B : Type} [CommRing B] [Algebra 𝒪 B] {C : Type} [CommRing C] [Algebra 𝒪 C] (χ : B →ₐ[𝒪] C) (f : B)
    (hf : IsUnit (χ f)) (b : B) :
    liftAway χ f hf (IsScalarTower.toAlgHom 𝒪 B (Localization.Away f) b) = χ b := by
  rw [IsScalarTower.coe_toAlgHom', liftAway, IsLocalization.liftAlgHom_apply, IsLocalization.lift_eq]
  rfl

theorem exists_num {B : Type} [CommRing B] [Algebra 𝒪 B] (f : B) (z : Localization.Away f) :
    ∃ (a : B) (n : ℕ), z * IsScalarTower.toAlgHom 𝒪 B (Localization.Away f) f ^ n =
      IsScalarTower.toAlgHom 𝒪 B (Localization.Away f) a := by
  obtain ⟨⟨a, y⟩, h⟩ := IsLocalization.surj (Submonoid.powers f) z
  obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff _ _).mp y.2
  refine ⟨a, n, ?_⟩
  change z * algebraMap B (Localization.Away f) f ^ n = algebraMap B (Localization.Away f) a
  rw [← map_pow, hn]
  exact h

theorem isNilpotent_algebraMap_of_algHom {B : Type} [CommRing B] [Algebra 𝒪 B] {C : Type} [CommRing C] [Algebra 𝒪 C]
    (π : 𝒪) (χ : B →ₐ[𝒪] C) (hB : IsNilpotent (algebraMap 𝒪 B π)) : IsNilpotent (algebraMap 𝒪 C π) := by
  obtain ⟨n, hn⟩ := hB
  exact ⟨n, by rw [← χ.commutes, ← map_pow, hn, map_zero]⟩

variable (π : 𝒪) (Onr : Type) [CommRing Onr] [Algebra 𝒪 Onr] (G : Type)

abbrev Src : AlgFunctor 𝒪 := AlgFunctor.prod (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)) (AlgFunctor.const G)

variable {π Onr G}

theorem src_map_mk {B : Type} [CommRing B] [Algebra 𝒪 B] {B' : Type} [CommRing B'] [Algebra 𝒪 B'] (φ : B →ₐ[𝒪] B')
    (ψ : Onr →ₐ[𝒪] B) (P : DeligneDatum (K := K₀) π B) (g : G) :
    (Src (K₀ := K₀) π Onr G).map φ ((ψ, P), g) = ((φ.comp ψ, P.map π φ), g) := rfl

theorem core (T : AlgFunctor 𝒪)
    (Θ : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B], IsNilpotent (algebraMap 𝒪 B π) → (Src (K₀ := K₀) π Onr G).obj B → T.obj B)
    (hnat : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (B' : Type) [CommRing B'] [Algebra 𝒪 B'] (hB : IsNilpotent (algebraMap 𝒪 B π))
      (hB' : IsNilpotent (algebraMap 𝒪 B' π)) (φ : B →ₐ[𝒪] B') (x : (Src (K₀ := K₀) π Onr G).obj B),
      Θ B' hB' ((Src (K₀ := K₀) π Onr G).map φ x) = T.map φ (Θ B hB x))
    (het : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (B₀ : Type) [CommRing B₀] [Algebra 𝒪 B₀] (p : B →ₐ[𝒪] B₀)
      (hB : IsNilpotent (algebraMap 𝒪 B π)) (hB₀ : IsNilpotent (algebraMap 𝒪 B₀ π)),
      Function.Surjective p → (∀ s t : B, p s = 0 → p t = 0 → s * t = 0) →
      ∀ (x₀ : (Src (K₀ := K₀) π Onr G).obj B₀) (y : T.obj B), T.map p y = Θ B₀ hB₀ x₀ →
        ∃! x : (Src (K₀ := K₀) π Onr G).obj B, (Src (K₀ := K₀) π Onr G).map p x = x₀ ∧ Θ B hB x = y)
    (S : Set Onr)
    (HA : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π)) (ψ ψ' : Onr →ₐ[𝒪] B)
      (P : DeligneDatum (K := K₀) π B) (g : G), (∀ y ∈ S, ψ y = ψ' y) → Θ B hB ((ψ, P), g) = Θ B hB ((ψ', P), g))
    {B : Type} [CommRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π))
    (ψ₁ ψ₂ : Onr →ₐ[𝒪] B) (P₁ P₂ : DeligneDatum (K := K₀) π B) (g : G)
    (hΘ : Θ B hB ((ψ₁, P₁), g) = Θ B hB ((ψ₂, P₂), g))
    {L : Type} [Field L] [Algebra 𝒪 L] (φ : B →ₐ[𝒪] L) (hP : P₁.map π φ = P₂.map π φ)
    (HH : ∃ (f : B) (s : Finset B), φ f ≠ 0 ∧ ∀ (C : Type) [CommRing C] [Algebra 𝒪 C] (χ : B →ₐ[𝒪] C), IsUnit (χ f) →
      (P₁.map π χ = P₂.map π χ ↔ ∀ b ∈ s, χ b = 0))
    (hcoef : ∃ f₀ : B, φ f₀ ≠ 0 ∧ ∀ (C : Type) [CommRing C] [Algebra 𝒪 C] (χ : B →ₐ[𝒪] C), IsUnit (χ f₀) →
      ∀ y ∈ S, χ (ψ₁ y) = χ (ψ₂ y)) :
    ∃ f : B, φ f ≠ 0 ∧ ∀ (C : Type) [CommRing C] [Algebra 𝒪 C] (χ : B →ₐ[𝒪] C), IsUnit (χ f) →
      P₁.map π χ = P₂.map π χ ∧ ∀ y ∈ S, χ (ψ₁ y) = χ (ψ₂ y) := by
  classical
  obtain ⟨f₀, hφ₀, H₀⟩ := hcoef
  obtain ⟨fH, s, hφH, HHs⟩ := HH

  set F : B := f₀ * fH with hF
  have hφF : φ F ≠ 0 := by rw [hF, map_mul]; exact mul_ne_zero hφ₀ hφH
  set B' : Type := Localization.Away F with hB'def
  set ι : B →ₐ[𝒪] B' := IsScalarTower.toAlgHom 𝒪 B B' with hι
  have hιF : IsUnit (ι F) := IsLocalization.Away.algebraMap_isUnit F
  have hι₀ : IsUnit (ι f₀) := isUnit_of_mul_isUnit_left (by rw [← map_mul]; exact hιF)
  have hιH : IsUnit (ι fH) := isUnit_of_mul_isUnit_right (by rw [← map_mul]; exact hιF)
  have hB' : IsNilpotent (algebraMap 𝒪 B' π) := isNilpotent_algebraMap_of_algHom π ι hB

  set φ' : B' →ₐ[𝒪] L := liftAway φ F (Ne.isUnit hφF) with hφ'
  have hφ'ι : ∀ b : B, φ' (ι b) = φ b := fun b => liftAway_apply φ F (Ne.isUnit hφF) b

  have hS' : ∀ y ∈ S, (ι.comp ψ₂) y = (ι.comp ψ₁) y := fun y hy => (H₀ B' ι hι₀ y hy).symm
  have e1 : Θ B' hB' ((ι.comp ψ₁, P₁.map π ι), g) = Θ B' hB' ((ι.comp ψ₂, P₂.map π ι), g) := by
    have h1 : Θ B' hB' ((ι.comp ψ₁, P₁.map π ι), g) = T.map ι (Θ B hB ((ψ₁, P₁), g)) := hnat B B' hB hB' ι ((ψ₁, P₁), g)
    have h2 : Θ B' hB' ((ι.comp ψ₂, P₂.map π ι), g) = T.map ι (Θ B hB ((ψ₂, P₂), g)) := hnat B B' hB hB' ι ((ψ₂, P₂), g)
    rw [h1, h2, hΘ]
  have EQ : Θ B' hB' ((ι.comp ψ₁, P₁.map π ι), g) = Θ B' hB' ((ι.comp ψ₁, P₂.map π ι), g) :=
    e1.trans (HA B' hB' (ι.comp ψ₂) (ι.comp ψ₁) (P₂.map π ι) g hS')

  set I : Ideal B' := Ideal.span ((s.image ι : Finset B') : Set B') with hI
  have hIfg : (I : Submodule B' B').FG := ⟨s.image ι, rfl⟩
  have hsI : ∀ b ∈ s, ι b ∈ I := fun b hb =>
    Ideal.subset_span (by rw [Finset.mem_coe, Finset.mem_image]; exact ⟨b, hb, rfl⟩)
  have hIχ : ∀ (C : Type) [CommRing C] [Algebra 𝒪 C] (χ'' : B' →ₐ[𝒪] C), (∀ b ∈ s, χ'' (ι b) = 0) →
      ∀ i ∈ I, χ'' i = 0 := by
    intro C _ _ χ'' hs i hi
    have hle : I ≤ RingHom.ker (χ'' : B' →+* C) := by
      rw [hI, Ideal.span_le]
      intro x hx
      rw [Finset.mem_coe, Finset.mem_image] at hx
      obtain ⟨b, hb, rfl⟩ := hx
      exact hs b hb
    exact hle hi

  set Q₂ : Type := B' ⧸ I ^ 2 with hQ₂
  set Q₁ : Type := B' ⧸ I with hQ₁
  set q₂ : B' →ₐ[𝒪] Q₂ := Ideal.Quotient.mkₐ 𝒪 (I ^ 2) with hq₂
  set q₁ : B' →ₐ[𝒪] Q₁ := Ideal.Quotient.mkₐ 𝒪 I with hq₁
  set p : Q₂ →ₐ[𝒪] Q₁ := Ideal.Quotient.factorₐ 𝒪 (Ideal.pow_le_self (I := I) (n := 2) two_ne_zero) with hp
  have hpq : ∀ x : B', p (q₂ x) = q₁ x := fun x => rfl
  have hp_comp : p.comp q₂ = q₁ := AlgHom.ext hpq
  have hp_surj : Function.Surjective p := by
    intro y
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mkₐ_surjective 𝒪 I y
    exact ⟨q₂ x, hpq x⟩
  have hp_sq : ∀ s₁ t₁ : Q₂, p s₁ = 0 → p t₁ = 0 → s₁ * t₁ = 0 := by
    intro s₁ t₁ hs ht
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mkₐ_surjective 𝒪 (I ^ 2) s₁
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mkₐ_surjective 𝒪 (I ^ 2) t₁
    change q₁ a = 0 at hs
    change q₁ b = 0 at ht
    rw [hq₁, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem] at hs ht
    rw [← map_mul, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem, pow_two]
    exact Ideal.mul_mem_mul hs ht
  have hQ₂ : IsNilpotent (algebraMap 𝒪 Q₂ π) := isNilpotent_algebraMap_of_algHom π q₂ hB'
  have hQ₁ : IsNilpotent (algebraMap 𝒪 Q₁ π) := isNilpotent_algebraMap_of_algHom π q₁ hB'

  set X₁ : (Src (K₀ := K₀) π Onr G).obj Q₂ := ((q₂.comp (ι.comp ψ₁), (P₁.map π ι).map π q₂), g) with hX₁
  set X₂ : (Src (K₀ := K₀) π Onr G).obj Q₂ := ((q₂.comp (ι.comp ψ₁), (P₂.map π ι).map π q₂), g) with hX₂
  have hX : Θ Q₂ hQ₂ X₁ = Θ Q₂ hQ₂ X₂ := by
    have h1 : Θ Q₂ hQ₂ X₁ = T.map q₂ (Θ B' hB' ((ι.comp ψ₁, P₁.map π ι), g)) :=
      hnat B' Q₂ hB' hQ₂ q₂ ((ι.comp ψ₁, P₁.map π ι), g)
    have h2 : Θ Q₂ hQ₂ X₂ = T.map q₂ (Θ B' hB' ((ι.comp ψ₁, P₂.map π ι), g)) :=
      hnat B' Q₂ hB' hQ₂ q₂ ((ι.comp ψ₁, P₂.map π ι), g)
    rw [h1, h2, EQ]

  have hu₁ : IsUnit (((p.comp q₂).comp ι) fH) := hιH.map (p.comp q₂)
  have hPP : P₁.map π ((p.comp q₂).comp ι) = P₂.map π ((p.comp q₂).comp ι) := by
    apply (HHs Q₁ ((p.comp q₂).comp ι) hu₁).mpr
    intro b hb
    show p (q₂ (ι b)) = 0
    rw [hpq, hq₁, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem]
    exact hsI b hb
  have hred : (Src (K₀ := K₀) π Onr G).map p X₂ = (Src (K₀ := K₀) π Onr G).map p X₁ := by
    have h : ((P₂.map π ι).map π q₂).map π p = ((P₁.map π ι).map π q₂).map π p := by
      change (Omega K₀ π).map p ((Omega K₀ π).map q₂ ((Omega K₀ π).map ι P₂)) =
        (Omega K₀ π).map p ((Omega K₀ π).map q₂ ((Omega K₀ π).map ι P₁))
      rw [← (Omega K₀ π).map_comp, ← (Omega K₀ π).map_comp, ← (Omega K₀ π).map_comp, ← (Omega K₀ π).map_comp]
      exact hPP.symm
    change (((p.comp (q₂.comp (ι.comp ψ₁)), ((P₂.map π ι).map π q₂).map π p), g) : (Src (K₀ := K₀) π Onr G).obj Q₁) =
      ((p.comp (q₂.comp (ι.comp ψ₁)), ((P₁.map π ι).map π q₂).map π p), g)
    rw [h]
    rfl

  obtain ⟨x, hx, huniq⟩ := het Q₂ Q₁ p hQ₂ hQ₁ hp_surj hp_sq ((Src (K₀ := K₀) π Onr G).map p X₁) (Θ Q₂ hQ₂ X₁)
    (hnat Q₂ Q₁ hQ₂ hQ₁ p X₁).symm
  have hX12 : X₁ = X₂ := (huniq X₁ ⟨rfl, rfl⟩).trans (huniq X₂ ⟨hred, hX.symm⟩).symm
  have hPq : (P₁.map π ι).map π q₂ = (P₂.map π ι).map π q₂ :=
    congrArg (fun z : (Src (K₀ := K₀) π Onr G).obj Q₂ => z.1.2) hX12

  have hsI2 : ∀ b ∈ s, ι b ∈ I ^ 2 := by
    have hu : IsUnit ((q₂.comp ι) fH) := hιH.map q₂
    have h := (HHs Q₂ (q₂.comp ι) hu).mp (by
      show (Omega K₀ π).map (q₂.comp ι) P₁ = (Omega K₀ π).map (q₂.comp ι) P₂
      rw [(Omega K₀ π).map_comp, (Omega K₀ π).map_comp]
      exact hPq)
    intro b hb
    have := h b hb
    change q₂ (ι b) = 0 at this
    rwa [hq₂, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem] at this
  have hII : I ≤ I • (I : Submodule B' B') := by
    rw [Ideal.smul_eq_mul, ← pow_two, hI, Ideal.span_le]
    intro x hx
    rw [Finset.mem_coe, Finset.mem_image] at hx
    obtain ⟨b, hb, rfl⟩ := hx
    exact hsI2 b hb
  obtain ⟨rr, hrr1, hrr⟩ := Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul I (I : Submodule B' B') hIfg hII

  have hφ'I : ∀ i ∈ I, φ' i = 0 :=
    hIχ L φ' (fun b hb => by rw [hφ'ι]; exact (HHs L φ (Ne.isUnit hφH)).mp hP b hb)
  have hφ'rr : φ' rr = 1 := by
    have := hφ'I _ hrr1
    rwa [map_sub, map_one, sub_eq_zero] at this
  obtain ⟨br, k, hbr⟩ := exists_num (𝒪 := 𝒪) F rr
  rw [← hι] at hbr
  refine ⟨br * F, ?_, ?_⟩
  · rw [map_mul]
    refine mul_ne_zero ?_ hφF
    have e := congrArg φ' hbr
    rw [map_mul, map_pow, hφ'ι, hφ'ι, hφ'rr, one_mul] at e
    rw [← e]
    exact pow_ne_zero _ hφF
  · intro C _ _ χ hχ
    have hχbr : IsUnit (χ br) := isUnit_of_mul_isUnit_left (by rw [← map_mul]; exact hχ)
    have hχF : IsUnit (χ F) := isUnit_of_mul_isUnit_right (by rw [← map_mul]; exact hχ)
    have hχ0 : IsUnit (χ f₀) := isUnit_of_mul_isUnit_left (by rw [← map_mul]; exact hχF)
    have hχH : IsUnit (χ fH) := isUnit_of_mul_isUnit_right (by rw [← map_mul]; exact hχF)
    refine ⟨?_, H₀ C χ hχ0⟩
    set χ' : B' →ₐ[𝒪] C := liftAway χ F hχF with hχ'
    have hχ'ι : ∀ b : B, χ' (ι b) = χ b := fun b => liftAway_apply χ F hχF b
    have hχ'rr : IsUnit (χ' rr) := by
      have e := congrArg χ' hbr
      rw [map_mul, map_pow, hχ'ι, hχ'ι] at e
      exact isUnit_of_mul_isUnit_left (by rw [e]; exact hχbr)
    have hχ'I : ∀ i ∈ I, χ' i = 0 := fun i hi => by
      have := congrArg χ' (hrr i hi)
      rw [smul_eq_mul, map_mul, map_zero] at this
      exact (hχ'rr.mul_right_eq_zero).mp this
    apply (HHs C χ hχH).mpr
    intro b hb
    rw [← hχ'ι]
    exact hχ'I _ (hsI b hb)

end Core

section Frame

theorem finite_of_isLevelTwistAction {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsOrder Λ) {N m : ℕ} [NeZero m]
    {B : Type} [CommRing B] {M : Scheme.{0}} {πM : M ⟶ Spec (CommRingCat.of B)}
    {ptF : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B)),
      FakeEllipticCurve.WithFullLevel Λ N m S → SchemeHomOver s πM}
    {G : Type} [Group G] {ρ : G →* Aut M} {χ : G → ↥Λ} (hρ : IsLevelTwistAction Λ N m M πM ptF G ρ χ) : Finite G := by
  classical
  set I : Ideal ℤ := Ideal.span {(m : ℤ)} with hI
  haveI : Module.Finite ℤ ↥Λ := Module.Finite.iff_fg.mpr hΛ.fg
  haveI : Finite (ℤ ⧸ I) := Finite.of_equiv (ZMod m) (Int.quotientSpanNatEquivZMod m).symm.toEquiv
  haveI : Module.Finite (ℤ ⧸ I) (↥Λ ⧸ (I • ⊤ : Submodule ℤ ↥Λ)) := inferInstance
  haveI : Finite (↥Λ ⧸ (I • ⊤ : Submodule ℤ ↥Λ)) := Module.finite_of_finite (ℤ ⧸ I)
  refine Finite.of_injective (fun g => Submodule.Quotient.mk (p := (I • ⊤ : Submodule ℤ ↥Λ)) (χ g)) ?_
  intro g g' hgg'
  apply hρ.label_injective g g'
  have hmem : χ g - χ g' ∈ (I • ⊤ : Submodule ℤ ↥Λ) := (Submodule.Quotient.eq _).mp hgg'
  rw [hI, Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists] at hmem
  obtain ⟨y, _, hy⟩ := hmem
  refine ⟨y, ?_⟩
  have := congrArg (fun z : ↥Λ => (z : ℍ[ℚ, a, b])) hy
  simp only [Submodule.coe_sub] at this
  rw [← this, Submodule.coe_smul_of_tower, ← Int.cast_smul_eq_zsmul ℚ, Int.cast_natCast]

variable {𝒪 : Type} [CommRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K] {π : 𝒪} {B : Type} [CommRing B] [Algebra 𝒪 B]

theorem isPullback_iff_eq_pullback (g : Matrix.GeneralLinearGroup (Fin 2) K) (d d' : DeligneDatum (K := K) π B) :
    DeligneDatum.IsPullback (K := K) (π := π) B g d d' ↔ d' = DeligneDatum.pullback π B g d := by
  constructor
  · intro h
    exact DeligneDatum.ext' (funext h)
  · intro h M
    rw [h]
    rfl

end Frame

end Q2SpreadT

end

theorem solution

    {r rbar N : ℕ} [Fact r.Prime] [Fact rbar.Prime] [NeZero N] (hrr : rbar ≠ r) (hrN : ¬ r ∣ N) (hrbarN : ¬ rbar ∣ N) (hN : Squarefree N)

    (𝒪 : Type) [CommRing 𝒪] [IsDomain 𝒪] [CharZero 𝒪] (hdvr : IsDiscreteValuationRing 𝒪)
    (π : 𝒪) (hπ : Irreducible π) (hcomplete : IsAdicComplete (Ideal.span {π}) 𝒪)
    (hres : Nat.card (𝒪 ⧸ Ideal.span {π}) = r) (hunr : Ideal.span {((r : ℕ) : 𝒪)} = Ideal.span {π})
    (K₀ : Type) [Field K₀] [CharZero K₀] [Algebra 𝒪 K₀] [IsFractionRing 𝒪 K₀]

    (Onr : Type) [CommRing Onr] [IsDomain Onr] [CharZero Onr] [Algebra 𝒪 Onr] (Fr : Onr ≃ₐ[𝒪] Onr)
    (hOnr_complete : IsAdicComplete (Ideal.span {algebraMap 𝒪 Onr π}) Onr)
    (hOnr_max : (Ideal.span {algebraMap 𝒪 Onr π}).IsMaximal)
    (hOnr_alg : ∀ x : Onr, ∃ p : Polynomial 𝒪, p.Monic ∧ Polynomial.aeval x p ∈ Ideal.span {algebraMap 𝒪 Onr π})
    (hOnr_closed : ∀ p : Polynomial Onr, p.Monic → 0 < p.natDegree → ∃ x : Onr, Polynomial.eval x p ∈ Ideal.span {algebraMap 𝒪 Onr π})
    (hFr : ∀ x : Onr, Fr x - x ^ r ∈ Ideal.span {algebraMap 𝒪 Onr π})
    (vdet : Matrix.GeneralLinearGroup (Fin 2) K₀ →* Multiplicative ℤ)
    (hvdet : ∀ (g : Matrix.GeneralLinearGroup (Fin 2) K₀) (n : ℤ), vdet g = Multiplicative.ofAdd n ↔
      ∃ u : 𝒪ˣ, (Matrix.GeneralLinearGroup.det g : K₀) = algebraMap 𝒪 K₀ (u : 𝒪) * (algebraMap 𝒪 K₀ π) ^ n)

    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b r rbar)
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (𝒳 : Scheme.{0}) (f : 𝒳 ⟶ Spec (CommRingCat.of 𝒪))
    (pt : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)), FakeEllipticCurve Λ N S → SchemeHomOver s f)
    (h𝒳 : IsCoarseModuli Λ N 𝒳 f pt)

    [hgr : GeometricallyReduced (Limits.pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 K₀))))]
    [hgc : GeometricallyConnected (Limits.pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 K₀))))]

    (n : ℕ) (hn : 3 ≤ n) (hrn : ¬ r ∣ n) (hrbarn : ¬ rbar ∣ n) (hnN : Nat.Coprime n N)
    (M : Scheme.{0}) (fM : M ⟶ Spec (CommRingCat.of 𝒪))
    (ptF : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)),
      FakeEllipticCurve.WithFullLevel Λ N n S → SchemeHomOver s fM)
    (hM : IsFineModuli Λ N n M fM ptF)
    (G : Type) [Group G] (ρ : G →* Aut M) (χ : G → ↥Λ) (hρ : IsLevelTwistAction Λ N n M fM ptF G ρ χ)

    (p : M ⟶ 𝒳) (hp : p ≫ f = fM) (hρp : ∀ h : G, (ρ h).hom ≫ p = p)
    (hp_pt : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)) (u : FakeEllipticCurve.WithFullLevel Λ N n S),
      (ptF S s u).1 ≫ p = (pt S s u.1).1)
    (𝒴 : HeckeTower.AwayPrime r rbar → Scheme.{0}) (g : ∀ ℓ : HeckeTower.AwayPrime r rbar, 𝒴 ℓ ⟶ Spec (CommRingCat.of 𝒪))
    (ptT : ∀ (ℓ : HeckeTower.AwayPrime r rbar) (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)),
      FakeEllipticCurve.WithExtraLevel Λ N (ℓ.1 : ℕ) S → SchemeHomOver s (g ℓ))
    (h𝒴 : ∀ ℓ : HeckeTower.AwayPrime r rbar, IsCoarseModuliT Λ N (ℓ.1 : ℕ) (𝒴 ℓ) (g ℓ) (ptT ℓ))
    (d₀ d₁ : ∀ ℓ : HeckeTower.AwayPrime r rbar, 𝒴 ℓ ⟶ 𝒳) (hd₀f : ∀ ℓ, d₀ ℓ ≫ f = g ℓ) (hd₁f : ∀ ℓ, d₁ ℓ ≫ f = g ℓ)
    (hd₀ : ∀ (ℓ : HeckeTower.AwayPrime r rbar) (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪))
      (u : FakeEllipticCurve.WithExtraLevel Λ N (ℓ.1 : ℕ) S), (ptT ℓ S s u).1 ≫ d₀ ℓ = (pt S s u.1).1)
    (hd₁ : ∀ (ℓ : HeckeTower.AwayPrime r rbar) (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪))
      (u : FakeEllipticCurve.WithExtraLevel Λ N (ℓ.1 : ℕ) S) (d : FakeEllipticCurve Λ N S),
      FakeEllipticCurve.IsLevelIsogeny (ℓ.1 : ℕ) u d → (ptT ℓ S s u).1 ≫ d₁ ℓ = (pt S s d).1)

    (ar arbar : 𝒳 ⟶ 𝒳) (harf : ar ≫ f = f) (harbarf : arbar ≫ f = f)
    (har : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)) (E E' : FakeEllipticCurve Λ N S),
      FakeEllipticCurve.IsAtkinLehnerQuotient r E E' → (pt S s E).1 ≫ ar = (pt S s E').1)
    (harbar : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)) (E E' : FakeEllipticCurve Λ N S),
      FakeEllipticCurve.IsAtkinLehnerQuotient rbar E E' → (pt S s E).1 ≫ arbar = (pt S s E').1)

    {a₁ b₁ : ℚ} (hdef : IsDefiniteRamifiedExactlyAt (a := a₁) (b := b₁) rbar)
    (Λ₁ R₁ : Submodule ℤ ℍ[ℚ, a₁, b₁]) (hΛ₁ : IsMaximalOrder Λ₁) (hR₁ : IsEichlerOrder R₁ N) (hRΛ₁ : R₁ ≤ Λ₁)
    (n₁ : (ℍ[ℚ, a₁, b₁] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) (hn₁ : n₁ ∈ primeHeckeSet R₁ r)
    (hS₁ : IsEichlerOrder (meetOrder R₁ n₁) (N * r))
    (ι₀ : ℍ[ℚ, a₁, b₁] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) K₀) (hι₀ : Function.Injective ι₀)
    (v : HeightOneSpectrum (𝓞 ℚ)) (hv : ((r : ℕ) : 𝓞 ℚ) ∈ v.asIdeal)

    (Γt : Subgroup (ℍ[ℚ, a₁, b₁])ˣ) (hΓt : ∀ x : (ℍ[ℚ, a₁, b₁])ˣ, x ∈ Γt ↔ x ∈ CerednikDrinfeld.CosetGraph.awayUnits R₁ v)
    (s : HeckeTower.AwayPrime r rbar → (ℍ[ℚ, a₁, b₁])ˣ)
    (sf : HeckeTower.AwayPrime r rbar → (ℍ[ℚ, a₁, b₁] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)
    (hs : ∀ ℓ : HeckeTower.AwayPrime r rbar,
      (∀ u : HeightOneSpectrum (𝓞 ℚ), ((r : ℕ) : 𝓞 ℚ) ∉ u.asIdeal →
        Submodule.finiteAdeleEvalAt ℍ[ℚ, a₁, b₁] u (sf ℓ : ℍ[ℚ, a₁, b₁] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) =
          (s ℓ : ℍ[ℚ, a₁, b₁]) ⊗ₜ[ℚ] (1 : u.adicCompletion ℚ)) ∧
      (∀ u : HeightOneSpectrum (𝓞 ℚ), ((r : ℕ) : 𝓞 ℚ) ∈ u.asIdeal →
        Submodule.finiteAdeleEvalAt ℍ[ℚ, a₁, b₁] u (sf ℓ : ℍ[ℚ, a₁, b₁] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) = 1) ∧
      Submodule.finiteIdeleDiagonal ℍ[ℚ, a₁, b₁]
          (Units.map (algebraMap ℚ ℍ[ℚ, a₁, b₁]).toMonoidHom
            (Units.mk0 ((ℓ.1 : ℕ) : ℚ) (Nat.cast_ne_zero.mpr ℓ.1.prop.ne_zero))) * (sf ℓ)⁻¹ ∈
        (if (ℓ.1 : ℕ) ∣ N then levelHeckeUSet Λ₁ (meetOrder R₁ n₁) (ℓ.1 : ℕ)
          else primeHeckeSet (meetOrder R₁ n₁) (ℓ.1 : ℕ)) ∧
      nrd (s ℓ : ℍ[ℚ, a₁, b₁]) = ((ℓ.1 : ℕ) : ℚ))
    (Γtℓ : HeckeTower.AwayPrime r rbar → Subgroup (ℍ[ℚ, a₁, b₁])ˣ) (hΓtℓ : ∀ ℓ : HeckeTower.AwayPrime r rbar, Γtℓ ℓ = Γt ⊓ Γt.map (MulAut.conj (s ℓ)).toMonoidHom)

    (wbar : (ℍ[ℚ, a₁, b₁])ˣ) (hwbar : nrd (wbar : ℍ[ℚ, a₁, b₁]) = ((rbar : ℕ) : ℚ) ∧ ∀ x : (ℍ[ℚ, a₁, b₁])ˣ, x ∈ Γt → wbar * x * wbar⁻¹ ∈ Γt)

    (θt : ↥Γt →* G)
      (Θf : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B], IsNilpotent (algebraMap 𝒪 B π) → (AlgFunctor.prod (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)) (AlgFunctor.const G)).obj B → (Scheme.nilpPoints fM).obj B)
      (ΘT : ∀ ℓ : HeckeTower.AwayPrime r rbar, ∀ (B : Type) [CommRing B] [Algebra 𝒪 B], IsNilpotent (algebraMap 𝒪 B π) → (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).obj B → (Scheme.nilpPoints (g ℓ)).obj B)

    (hnat :
      (∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (B' : Type) [CommRing B'] [Algebra 𝒪 B'] (hB : IsNilpotent (algebraMap 𝒪 B π))
          (hB' : IsNilpotent (algebraMap 𝒪 B' π)) (φ : B →ₐ[𝒪] B') (x : (AlgFunctor.prod (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)) (AlgFunctor.const G)).obj B),
          Θf B' hB' ((AlgFunctor.prod (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)) (AlgFunctor.const G)).map φ x) = (Scheme.nilpPoints fM).map φ (Θf B hB x)))

    (hG :
      (∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π)) (x : (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).obj B) (g h : G),
          (Scheme.nilpPoints.mapHom fM fM (ρ h).hom (hρ.over_base h)).app B (Θf B hB (x, g * h)) = Θf B hB (x, g)))

    (hinv :
      (∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π)) (γ : (ℍ[ℚ, a₁, b₁])ˣ) (hγ : γ ∈ Γt)
          (x x' : (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).obj B) (g : G),
          OmegaNr.IsTwistedAct π Onr Fr vdet B ((Units.map (ι₀ : ℍ[ℚ, a₁, b₁] →* Matrix (Fin 2) (Fin 2) K₀)) γ) x x' → Θf B hB (x', θt ⟨γ, hγ⟩ * g) = Θf B hB (x, g)))

    (het :
      (∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (B₀ : Type) [CommRing B₀] [Algebra 𝒪 B₀] (p : B →ₐ[𝒪] B₀)
          (hB : IsNilpotent (algebraMap 𝒪 B π)) (hB₀ : IsNilpotent (algebraMap 𝒪 B₀ π)),
          Function.Surjective p → (∀ s t : B, p s = 0 → p t = 0 → s * t = 0) →
          ∀ (x₀ : (AlgFunctor.prod (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)) (AlgFunctor.const G)).obj B₀) (y : (Scheme.nilpPoints fM).obj B), (Scheme.nilpPoints fM).map p y = Θf B₀ hB₀ x₀ →
            ∃! x : (AlgFunctor.prod (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)) (AlgFunctor.const G)).obj B, (AlgFunctor.prod (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)) (AlgFunctor.const G)).map p x = x₀ ∧ Θf B hB x = y))
    (ℓ : HeckeTower.AwayPrime r rbar)
    (Mℓ : Scheme.{0}) (fMℓ : Mℓ ⟶ Spec (CommRingCat.of 𝒪))

    (Θfℓ : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B], IsNilpotent (algebraMap 𝒪 B π) → (AlgFunctor.prod (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)) (AlgFunctor.const G)).obj B → (Scheme.nilpPoints fMℓ).obj B)

    (hnatℓ :
    (∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (B' : Type) [CommRing B'] [Algebra 𝒪 B'] (hB : IsNilpotent (algebraMap 𝒪 B π))
        (hB' : IsNilpotent (algebraMap 𝒪 B' π)) (φ : B →ₐ[𝒪] B') (x : (AlgFunctor.prod (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)) (AlgFunctor.const G)).obj B),
        Θfℓ B' hB' ((AlgFunctor.prod (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)) (AlgFunctor.const G)).map φ x) = (Scheme.nilpPoints fMℓ).map φ (Θfℓ B hB x)))

    (hinvℓ :
    (∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π)) (γ : (ℍ[ℚ, a₁, b₁])ˣ) (hγ : γ ∈ Γt) (hγℓ : γ ∈ Γtℓ ℓ)
        (x x' : (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).obj B) (g : G),
        OmegaNr.IsTwistedAct π Onr Fr vdet B ((Units.map (ι₀ : ℍ[ℚ, a₁, b₁] →* Matrix (Fin 2) (Fin 2) K₀)) γ) x x' → Θfℓ B hB (x', θt ⟨γ, hγ⟩ * g) = Θfℓ B hB (x, g)))

    (hetℓ :
    (∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (B₀ : Type) [CommRing B₀] [Algebra 𝒪 B₀] (p : B →ₐ[𝒪] B₀)
        (hB : IsNilpotent (algebraMap 𝒪 B π)) (hB₀ : IsNilpotent (algebraMap 𝒪 B₀ π)),
        Function.Surjective p → (∀ s t : B, p s = 0 → p t = 0 → s * t = 0) →
        ∀ (x₀ : (AlgFunctor.prod (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)) (AlgFunctor.const G)).obj B₀) (y : (Scheme.nilpPoints fMℓ).obj B), (Scheme.nilpPoints fMℓ).map p y = Θfℓ B₀ hB₀ x₀ →
          ∃! x : (AlgFunctor.prod (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)) (AlgFunctor.const G)).obj B, (AlgFunctor.prod (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)) (AlgFunctor.const G)).map p x = x₀ ∧ Θfℓ B hB x = y))

    (hfMℓ : LocallyOfFiniteType fMℓ)
    :

    ∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π))
      (x₁ x₂ : (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).obj B) (g₁ g₂ : G),
      Θfℓ B hB (x₁, g₁) = Θfℓ B hB (x₂, g₂) →
      ∀ (L : Type) [Field L] [Algebra 𝒪 L] (φ : B →ₐ[𝒪] L) (γ : (ℍ[ℚ, a₁, b₁])ˣ) (hγ : γ ∈ Γt) (hγℓ : γ ∈ Γtℓ ℓ),
        (DeligneDatum.IsPullback (K := K₀) (π := π) L ((Units.map (ι₀ : ℍ[ℚ, a₁, b₁] →* Matrix (Fin 2) (Fin 2) K₀)) γ)⁻¹ ((AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).map φ x₁).2 ((AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).map φ x₂).2 ∧
          (∀ y : Onr, (∀ (z : (ℍ[ℚ, a₁, b₁])ˣ) (hz : z ∈ Γt), (∃ c : ℚ, (z : ℍ[ℚ, a₁, b₁]) = c • (1 : ℍ[ℚ, a₁, b₁])) →
              θt ⟨z, hz⟩ = 1 → (Fr ^ Multiplicative.toAdd (vdet ((Units.map (ι₀ : ℍ[ℚ, a₁, b₁] →* Matrix (Fin 2) (Fin 2) K₀)) z))) y = y) →
            (show Onr →ₐ[𝒪] L from ((AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).map φ x₂).1) y =
              frobTwist Onr Fr (- Multiplicative.toAdd (vdet ((Units.map (ι₀ : ℍ[ℚ, a₁, b₁] →* Matrix (Fin 2) (Fin 2) K₀)) γ))) (show Onr →ₐ[𝒪] L from ((AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).map φ x₁).1) y) ∧
          g₂ = θt ⟨γ, hγ⟩ * g₁) →
        ∃ f : B, φ f ≠ 0 ∧
          ∀ (C : Type) [CommRing C] [Algebra 𝒪 C] (χ : B →ₐ[𝒪] C), IsUnit (χ f) →
            DeligneDatum.IsPullback (K := K₀) (π := π) C ((Units.map (ι₀ : ℍ[ℚ, a₁, b₁] →* Matrix (Fin 2) (Fin 2) K₀)) γ)⁻¹ ((AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).map χ x₁).2 ((AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).map χ x₂).2 ∧
            (∀ y : Onr, (∀ (z : (ℍ[ℚ, a₁, b₁])ˣ) (hz : z ∈ Γt), (∃ c : ℚ, (z : ℍ[ℚ, a₁, b₁]) = c • (1 : ℍ[ℚ, a₁, b₁])) →
              θt ⟨z, hz⟩ = 1 → (Fr ^ Multiplicative.toAdd (vdet ((Units.map (ι₀ : ℍ[ℚ, a₁, b₁] →* Matrix (Fin 2) (Fin 2) K₀)) z))) y = y) →
              (show Onr →ₐ[𝒪] C from ((AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).map χ x₂).1) y =
                frobTwist Onr Fr (- Multiplicative.toAdd (vdet ((Units.map (ι₀ : ℍ[ℚ, a₁, b₁] →* Matrix (Fin 2) (Fin 2) K₀)) γ))) (show Onr →ₐ[𝒪] C from ((AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).map χ x₁).1) y) ∧
            g₂ = θt ⟨γ, hγ⟩ * g₁ := by
  intro B _ _ hBπ x₁ x₂ g₁ g₂ hΘ12 L _ _ φ γ hγ hγℓ hrel
  obtain ⟨hPB, hψ, hg⟩ := hrel
  classical
  haveI := hdvr
  have hrp : r.Prime := Fact.out

  set gγ : Matrix.GeneralLinearGroup (Fin 2) K₀ := (Units.map (ι₀ : ℍ[ℚ, a₁, b₁] →* Matrix (Fin 2) (Fin 2) K₀)) γ with hgγ
  set vγ : ℤ := Multiplicative.toAdd (vdet gγ) with hvγ
  set ψ₁' : Onr →ₐ[𝒪] B := frobTwist Onr Fr (-vγ) x₁.1 with hψ₁'
  set P₁' : DeligneDatum (K := K₀) π B := DeligneDatum.pullback π B gγ⁻¹ x₁.2 with hP₁'
  have htw : OmegaNr.IsTwistedAct π Onr Fr vdet B gγ x₁ (ψ₁', P₁') :=
    ⟨rfl, DeligneDatum.isPullback_pullback π B gγ⁻¹ x₁.2⟩
  have hΘ' : Θfℓ B hBπ ((ψ₁', P₁'), g₂) = Θfℓ B hBπ ((x₂.1, x₂.2), g₂) := by
    have h1 := hinvℓ B hBπ γ hγ hγℓ x₁ (ψ₁', P₁') g₁ htw
    rw [← hg] at h1
    rw [h1, hΘ12]
    rfl

  have hfin : Finite (𝒪 ⧸ Ideal.span {π}) := Nat.finite_of_card_ne_zero (by rw [hres]; exact hrp.ne_zero)

  have hPφ : P₁'.map π φ = x₂.2.map π φ := by
    have h1 := (Q2SpreadT.isPullback_iff_eq_pullback gγ⁻¹ _ _).mp hPB
    change x₂.2.map π φ = DeligneDatum.pullback π L gγ⁻¹ (x₁.2.map π φ) at h1
    rw [h1, hP₁', DeligneDatum.map_pullback]
  have HH := CerednikDrinfeld.FormalOmega.DeligneDatum.exists_finset_forall_map_eq_iff_of_map_eq (K := K₀) hπ hfin hBπ P₁' x₂.2 φ hPφ

  haveI : NeZero n := ⟨by omega⟩
  haveI hGfin : Finite G := Q2SpreadT.finite_of_isLevelTwistAction hΛ.isOrder hρ
  set kG : ℕ := Nat.card G with hkG
  have hkG_pos : 0 < kG := Nat.card_pos
  set cU : ℚˣ := Units.mk0 (r : ℚ) (Nat.cast_ne_zero.mpr hrp.ne_zero) with hcU
  have hcval : ∀ p' : ℕ, p'.Prime → p' ≠ r → padicValRat p' (cU : ℚ) = 0 := by
    intro p' hp' hne
    haveI : Fact p'.Prime := ⟨hp'⟩
    show padicValRat p' ((r : ℕ) : ℚ) = 0
    rw [padicValRat.of_nat, padicValNat_primes hne, Nat.cast_zero]
  set zr : (ℍ[ℚ, a₁, b₁])ˣ := Units.map (algebraMap ℚ ℍ[ℚ, a₁, b₁]).toMonoidHom cU with hzr
  have hzrΓ : zr ∈ Γt := (hΓt zr).mpr
    ((CerednikDrinfeld.CosetGraph.padicValRat_nrd_eq_zero_of_mem_awayUnits R₁ hR₁.isOrder r v hv).2 cU hcval)
  have hzr_val : (zr : ℍ[ℚ, a₁, b₁]) = (r : ℚ) • (1 : ℍ[ℚ, a₁, b₁]) := by
    rw [hzr, Units.coe_map]
    show algebraMap ℚ ℍ[ℚ, a₁, b₁] (r : ℚ) = _
    rw [Algebra.algebraMap_eq_smul_one]
  set z₀ : (ℍ[ℚ, a₁, b₁])ˣ := zr ^ kG with hz₀
  have hz₀Γ : z₀ ∈ Γt := Γt.pow_mem hzrΓ kG
  have hz₀_central : ∃ c : ℚ, (z₀ : ℍ[ℚ, a₁, b₁]) = c • (1 : ℍ[ℚ, a₁, b₁]) :=
    ⟨(r : ℚ) ^ kG, by rw [hz₀, Units.val_pow_eq_pow_val, hzr_val, smul_pow, one_pow]⟩
  have hθz₀ : θt ⟨z₀, hz₀Γ⟩ = 1 := by
    have e : (⟨z₀, hz₀Γ⟩ : ↥Γt) = ⟨zr, hzrΓ⟩ ^ kG := Subtype.ext rfl
    rw [e, map_pow, hkG, pow_card_eq_one']

  have hassoc : Associated ((r : ℕ) : 𝒪) π := Ideal.span_singleton_eq_span_singleton.mp hunr
  obtain ⟨u, hu⟩ := hassoc
  have hr𝒪 : ((r : ℕ) : 𝒪) = π * (↑u⁻¹ : 𝒪) := by rw [← hu, mul_assoc, Units.mul_inv, mul_one]
  have hvdet_zr : vdet ((Units.map (ι₀ : ℍ[ℚ, a₁, b₁] →* Matrix (Fin 2) (Fin 2) K₀)) zr) = Multiplicative.ofAdd (2 : ℤ) := by
    apply (hvdet _ 2).mpr
    refine ⟨u⁻¹ ^ 2, ?_⟩
    rw [Matrix.GeneralLinearGroup.val_det_apply, Units.coe_map]
    change (ι₀ (zr : ℍ[ℚ, a₁, b₁])).det = _
    rw [hzr_val, map_smul, map_one, ← algebraMap_smul K₀ (r : ℚ) (1 : Matrix (Fin 2) (Fin 2) K₀), Matrix.det_smul,
      Matrix.det_one, mul_one, Fintype.card_fin, map_natCast, zpow_ofNat, Units.val_pow_eq_pow_val, map_pow, ← mul_pow,
      ← map_mul, ← map_natCast (algebraMap 𝒪 K₀) r, hr𝒪, mul_comm π]
  have hvdet_z₀ : Multiplicative.toAdd (vdet ((Units.map (ι₀ : ℍ[ℚ, a₁, b₁] →* Matrix (Fin 2) (Fin 2) K₀)) z₀)) = ((2 * kG : ℕ) : ℤ) := by
    rw [hz₀, map_pow, map_pow, hvdet_zr, ← ofAdd_nsmul, toAdd_ofAdd, nsmul_eq_mul]
    push_cast
    ring

  set mq : ℕ := 2 * kG with hmq
  have hmq_pos : 0 < mq := by omega
  set q : ℕ := r ^ mq with hq
  have hq2 : 2 ≤ q := le_trans hrp.two_le (Nat.le_self_pow hmq_pos.ne' r)
  set Fam : Set (Onr ≃ₐ[𝒪] Onr) := {σ | ∃ (z : (ℍ[ℚ, a₁, b₁])ˣ) (hz : z ∈ Γt),
      (∃ c : ℚ, (z : ℍ[ℚ, a₁, b₁]) = c • (1 : ℍ[ℚ, a₁, b₁])) ∧ θt ⟨z, hz⟩ = 1 ∧
      σ = Fr ^ Multiplicative.toAdd (vdet ((Units.map (ι₀ : ℍ[ℚ, a₁, b₁] →* Matrix (Fin 2) (Fin 2) K₀)) z))} with hFam
  have hmemS : ∀ y : Onr, y ∈ Q2SpreadT.Fix Fam ↔
      (∀ (z : (ℍ[ℚ, a₁, b₁])ˣ) (hz : z ∈ Γt), (∃ c : ℚ, (z : ℍ[ℚ, a₁, b₁]) = c • (1 : ℍ[ℚ, a₁, b₁])) →
        θt ⟨z, hz⟩ = 1 → (Fr ^ Multiplicative.toAdd (vdet ((Units.map (ι₀ : ℍ[ℚ, a₁, b₁] →* Matrix (Fin 2) (Fin 2) K₀)) z))) y = y) := by
    intro y
    constructor
    · intro hy z hz hc hθ
      exact hy _ ⟨z, hz, hc, hθ, rfl⟩
    · rintro hy σ ⟨z, hz, hc, hθ, rfl⟩
      exact hy z hz hc hθ
  set σ₀ : Onr ≃ₐ[𝒪] Onr := Fr ^ Multiplicative.toAdd (vdet ((Units.map (ι₀ : ℍ[ℚ, a₁, b₁] →* Matrix (Fin 2) (Fin 2) K₀)) z₀)) with hσ₀
  have hσ₀Fam : σ₀ ∈ Fam := ⟨z₀, hz₀Γ, hz₀_central, hθz₀, rfl⟩
  have hσ₀_eq : σ₀ = Fr ^ mq := by rw [hσ₀, hvdet_z₀, zpow_natCast]

  set ϖ : Onr := algebraMap 𝒪 Onr π with hϖ
  have hpow_sub_mem : ∀ (a' b' : Onr) (k : ℕ), a' - b' ∈ Ideal.span {ϖ} → a' ^ k - b' ^ k ∈ Ideal.span {ϖ} := by
    intro a' b' k h
    obtain ⟨c, hc⟩ := sub_dvd_pow_sub_pow a' b' k
    rw [hc]; exact Ideal.mul_mem_right _ _ h
  have hFrk : ∀ (k : ℕ) (y : Onr), (Fr ^ k) y - y ^ r ^ k ∈ Ideal.span {ϖ} := by
    intro k
    induction k with
    | zero =>
      intro y
      rw [pow_zero, pow_zero, pow_one, AlgEquiv.one_apply, sub_self]
      exact Ideal.zero_mem _
    | succ k ih =>
      intro y
      have h1 := hFr ((Fr ^ k) y)
      have h2 := hpow_sub_mem _ _ r (ih y)
      have e : (Fr ^ (k + 1)) y - y ^ r ^ (k + 1) =
          (Fr ((Fr ^ k) y) - ((Fr ^ k) y) ^ r) + (((Fr ^ k) y) ^ r - (y ^ r ^ k) ^ r) := by
        rw [pow_succ', AlgEquiv.mul_apply, ← pow_mul, ← pow_succ]; ring
      rw [e]; exact Ideal.add_mem _ h1 h2
  have hσ₀q : ∀ y : Onr, σ₀ y - y ^ q ∈ Ideal.span {ϖ} := by
    intro y; rw [hσ₀_eq, hq]; exact hFrk mq y

  have hϖ0 : ϖ ≠ 0 := by
    intro h0
    apply hrp.ne_zero
    have : ((r : ℕ) : Onr) = 0 := by
      rw [← map_natCast (algebraMap 𝒪 Onr), hr𝒪, map_mul, ← hϖ, h0, zero_mul]
    exact_mod_cast this
  have hqI : ((q : ℕ) : Onr) ∈ Ideal.span {ϖ} := by
    have hrI : ((r : ℕ) : Onr) ∈ Ideal.span {ϖ} := by
      rw [← map_natCast (algebraMap 𝒪 Onr), hr𝒪, map_mul]
      exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
    rw [hq, Nat.cast_pow]
    exact Ideal.pow_mem_of_mem _ hrI mq hmq_pos
  have hqB : IsNilpotent ((q : ℕ) : B) := by
    have hrB : IsNilpotent ((r : ℕ) : B) := by
      rw [← map_natCast (algebraMap 𝒪 B), hr𝒪, map_mul]
      exact Commute.isNilpotent_mul_right (Commute.all _ _) hBπ
    rw [hq, Nat.cast_pow]
    exact hrB.pow_of_pos hmq_pos.ne'

  have hcoef := Q2SpreadT.coeff_spread (Fam := Fam) hOnr_complete hq2 hqI hϖ0 σ₀ hσ₀Fam hσ₀q hBπ hqB ψ₁' x₂.1 φ (by
    intro y hy
    exact (hψ y ((hmemS y).mp hy)).symm)

  have HA : ∀ (B₂ : Type) [CommRing B₂] [Algebra 𝒪 B₂] (hB₂ : IsNilpotent (algebraMap 𝒪 B₂ π)) (ψ ψ' : Onr →ₐ[𝒪] B₂)
      (P : DeligneDatum (K := K₀) π B₂) (g' : G), (∀ y ∈ Q2SpreadT.Fix Fam, ψ y = ψ' y) →
      Θfℓ B₂ hB₂ ((ψ, P), g') = Θfℓ B₂ hB₂ ((ψ', P), g') := by
    intro B₂ _ _ hB₂ ψ ψ' P g' hS
    exact CerednikDrinfeld.QM.IsFineModuliT.cerednikDrinfeld_uniformization_fine_eq_of_forall_frobFixed_eq
      hrr hrN hrbarN hN 𝒪 hdvr π hπ hcomplete hres hunr K₀ Onr Fr hOnr_complete hOnr_max hOnr_alg hOnr_closed hFr vdet hvdet hB Λ hΛ
      𝒳 f pt h𝒳 n hn hrn hrbarn hnN M fM ptF hM G ρ χ hρ p hp hρp hp_pt 𝒴 g ptT h𝒴 d₀ d₁ hd₀f hd₁f hd₀ hd₁ ar arbar harf harbarf
      har harbar hdef Λ₁ R₁ hΛ₁ hR₁ hRΛ₁ n₁ hn₁ hS₁ ι₀ hι₀ v hv Γt hΓt s sf hs Γtℓ hΓtℓ wbar hwbar θt Θf ΘT hnat hG hinv het
      ℓ Mℓ fMℓ Θfℓ hnatℓ hinvℓ hfMℓ B₂ hB₂ ψ ψ' P g' (fun y hy => hS y ((hmemS y).mpr hy))

  obtain ⟨fS, hφfS, HfS⟩ := Q2SpreadT.core (K₀ := K₀) (π := π) (Onr := Onr) (G := G) (Scheme.nilpPoints fMℓ) Θfℓ hnatℓ hetℓ
    (Q2SpreadT.Fix Fam) HA hBπ ψ₁' x₂.1 P₁' x₂.2 g₂ hΘ' φ hPφ HH hcoef
  refine ⟨fS, hφfS, ?_⟩
  intro C _ _ χ' hχ'
  obtain ⟨hPC, hSC⟩ := HfS C χ' hχ'
  refine ⟨?_, ?_, hg⟩
  · apply (Q2SpreadT.isPullback_iff_eq_pullback gγ⁻¹ _ _).mpr
    change x₂.2.map π χ' = DeligneDatum.pullback π C gγ⁻¹ (x₁.2.map π χ')
    rw [← hPC, hP₁', DeligneDatum.map_pullback]
  · intro y hy
    exact (hSC y ((hmemS y).mpr hy)).symm

end S_CerednikDrinfeld_QM_IsFineModuliT_exists_apply_ne_zero_forall_isPullback_of_cerednikDrinfeld_uniformization_fine_eq
end P2MW
export P2MW.S_CerednikDrinfeld_QM_IsFineModuliT_exists_apply_ne_zero_forall_isPullback_of_cerednikDrinfeld_uniformization_fine_eq (solution)
