-- Prove2me | solution 1 for CerednikDrinfeld.QM.IsFineModuliT.cerednikDrinfeld_uniformization_fine_eq_of_forall_frobFixed_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/9b6b8fae-025b-5366-bcb0-e2bc6857fc38

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
import Theorems.Thm_AlgebraicGeometry_Scheme_nilpPoints_exists_subalgebra_fg_map_eq_of_locallyOfFiniteType
import Theorems.Thm_CerednikDrinfeld_FormalOmega_Omega_action_scalarGL
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_IsFineModuliT_cerednikDrinfeld_uniformization_fine_eq_of_forall_frobFixed_eq

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory AlgebraicGeometry QuaternionAlgebra IsDedekindDomain CerednikDrinfeld CerednikDrinfeld.QM CerednikDrinfeld.FormalOmega NeronModelInfra LT.LatticeTree

noncomputable section

namespace Q2CoeffT

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

theorem isUnit_of_not_mem (I : Ideal R) (hmax : I.IsMaximal) (hI : I ≤ Ideal.jacobson ⊥) (x : R) (hx : x ∉ I) :
    IsUnit x := by
  obtain ⟨y, i, hi, h⟩ := hmax.exists_inv hx
  have hu : IsUnit (i * (-1) + 1) := Ideal.mem_jacobson_bot.mp (hI hi) (-1)
  have e : i * (-1) + 1 = y * x := by linear_combination -h
  rw [e] at hu
  exact isUnit_of_mul_isUnit_right hu

theorem isUnit_sub_of_pow_eq (I : Ideal R) (hmax : I.IsMaximal) (hI : I ≤ Ideal.jacobson ⊥) (q : ℕ)
    (hq : (q : R) ∈ I) (a b : R) (ha : a ^ q = a) (hb : b ^ q = b) (hab : a ≠ b) : IsUnit (a - b) := by
  apply isUnit_of_not_mem I hmax hI
  intro hmem
  apply hab
  apply eq_of_pow_eq_of_sub_mem I hI q hq a b ha hb
  have : b - a = -(a - b) := by ring
  rw [this]; exact I.neg_mem hmem

end Teichmuller

section Digits

variable {𝒪 : Type} [CommRing 𝒪] {Onr : Type} [CommRing Onr] [Algebra 𝒪 Onr]

theorem map_mem_span (π : 𝒪) (σ : Onr ≃ₐ[𝒪] Onr) (x : Onr) (hx : x ∈ Ideal.span {algebraMap 𝒪 Onr π}) :
    σ x ∈ Ideal.span {algebraMap 𝒪 Onr π} := by
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hx
  rw [map_mul, AlgEquiv.commutes]
  exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)

theorem pow_apply_eq_self_of_apply_eq_self (σ : Onr ≃ₐ[𝒪] Onr) (y : Onr) (h : σ y = y) (n : ℕ) : (σ ^ n) y = y := by
  induction n with
  | zero => rw [pow_zero, AlgEquiv.one_apply]
  | succ n ih => rw [pow_succ, AlgEquiv.mul_apply, h, ih]

theorem zpow_apply_eq_self_of_apply_eq_self (σ : Onr ≃ₐ[𝒪] Onr) (y : Onr) (h : σ y = y) (n : ℤ) : (σ ^ n) y = y := by
  obtain ⟨k, rfl | rfl⟩ := Int.eq_nat_or_neg n
  · rw [zpow_natCast]; exact pow_apply_eq_self_of_apply_eq_self σ y h k
  · rw [zpow_neg, zpow_natCast]
    have hk := pow_apply_eq_self_of_apply_eq_self σ y h k
    conv_lhs => rw [← hk]
    exact (σ ^ k).symm_apply_apply y

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

theorem algEquiv_digits (σ : Onr ≃ₐ[𝒪] Onr) {e : ℕ} (ts : Fin e → Onr) (y' : Onr) :
    σ ((∑ j, ts j * algebraMap 𝒪 Onr π ^ (j : ℕ)) + algebraMap 𝒪 Onr π ^ e * y') =
      (∑ j, σ (ts j) * algebraMap 𝒪 Onr π ^ (j : ℕ)) + algebraMap 𝒪 Onr π ^ e * σ y' := by
  rw [map_add, map_mul, map_pow, AlgEquiv.commutes, map_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  rw [map_mul, map_pow, AlgEquiv.commutes]

variable (Fr : Onr ≃ₐ[𝒪] Onr) (r : ℕ)

theorem frob_pow_sub_mem (hFr : ∀ x : Onr, Fr x - x ^ r ∈ Ideal.span {algebraMap 𝒪 Onr π}) :
    ∀ (k : ℕ) (y : Onr), (Fr ^ k) y - y ^ r ^ k ∈ Ideal.span {algebraMap 𝒪 Onr π} := by
  have hpow_sub_mem : ∀ (a' b' : Onr) (k : ℕ), a' - b' ∈ Ideal.span {algebraMap 𝒪 Onr π} →
      a' ^ k - b' ^ k ∈ Ideal.span {algebraMap 𝒪 Onr π} := by
    intro a' b' k h
    obtain ⟨c, hc⟩ := sub_dvd_pow_sub_pow a' b' k
    rw [hc]; exact Ideal.mul_mem_right _ _ h
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

variable {Fr r}

theorem frob_teich (hjac : Ideal.span {algebraMap 𝒪 Onr π} ≤ Ideal.jacobson ⊥)
    (hFr : ∀ x : Onr, Fr x - x ^ r ∈ Ideal.span {algebraMap 𝒪 Onr π})
    (Q : ℕ) (hQ : (Q : Onr) ∈ Ideal.span {algebraMap 𝒪 Onr π}) (t : Onr) (ht : t ^ Q = t) : Fr t = t ^ r := by
  symm
  apply eq_of_pow_eq_of_sub_mem _ hjac Q hQ (t ^ r) (Fr t)
  · rw [← pow_mul, mul_comm, pow_mul, ht]
  · rw [← map_pow, ht]
  · exact hFr t

theorem frob_pow_teich (hjac : Ideal.span {algebraMap 𝒪 Onr π} ≤ Ideal.jacobson ⊥)
    (hFr : ∀ x : Onr, Fr x - x ^ r ∈ Ideal.span {algebraMap 𝒪 Onr π})
    (Q : ℕ) (hQ : (Q : Onr) ∈ Ideal.span {algebraMap 𝒪 Onr π}) (t : Onr) (ht : t ^ Q = t) (n : ℕ) :
    (Fr ^ n) t = t ^ r ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, pow_one, AlgEquiv.one_apply]
  | succ n ih =>
    have htn : (t ^ r ^ n) ^ Q = t ^ r ^ n := by rw [← pow_mul, mul_comm, pow_mul, ht]
    rw [pow_succ', AlgEquiv.mul_apply, ih, frob_teich hjac hFr Q hQ _ htn, ← pow_mul, ← pow_succ]

theorem pow_teich (Q : ℕ) (t : Onr) (ht : t ^ Q = t) (n : ℕ) : (t ^ n) ^ Q = t ^ n := by
  rw [← pow_mul, mul_comm, pow_mul, ht]

theorem exists_frob_pow_fixed_sub_mem
    (hcomplete : IsAdicComplete (Ideal.span {algebraMap 𝒪 Onr π}) Onr)
    (hmax : (Ideal.span {algebraMap 𝒪 Onr π}).IsMaximal)
    (halg : ∀ x : Onr, ∃ p : Polynomial 𝒪, p.Monic ∧ Polynomial.aeval x p ∈ Ideal.span {algebraMap 𝒪 Onr π})
    (hFr : ∀ x : Onr, Fr x - x ^ r ∈ Ideal.span {algebraMap 𝒪 Onr π})
    (hr2 : 2 ≤ r) (hrI : ((r : ℕ) : Onr) ∈ Ideal.span {algebraMap 𝒪 Onr π}) (a : Onr) :
    ∃ k : ℕ, 0 < k ∧ ∃ t : Onr, (Fr ^ k) t = t ∧ a - t ∈ Ideal.span {algebraMap 𝒪 Onr π} := by
  classical
  set I : Ideal Onr := Ideal.span {algebraMap 𝒪 Onr π} with hIdef
  haveI := hcomplete
  haveI : HenselianRing Onr I := IsAdicComplete.henselianRing Onr _
  have hjac : I ≤ Ideal.jacobson ⊥ := IsAdicComplete.le_jacobson_bot _
  haveI : I.IsPrime := hmax.isPrime
  haveI : Nontrivial (Onr ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hmax.ne_top
  obtain ⟨p, hpm, hpa⟩ := halg a

  set pk : (Onr ⧸ I)[X] := (p.map (algebraMap 𝒪 Onr)).map (Ideal.Quotient.mk I) with hpk
  have hpk0 : pk ≠ 0 := ((hpm.map _).map _).ne_zero
  set T : Finset (Onr ⧸ I) := pk.roots.toFinset with hT
  have hroot : ∀ n : ℕ, Ideal.Quotient.mk I ((Fr ^ n) a) ∈ T := by
    intro n
    rw [hT, Multiset.mem_toFinset, mem_roots hpk0, IsRoot.def, hpk, Polynomial.eval_map, Polynomial.eval₂_at_apply,
      Ideal.Quotient.eq_zero_iff_mem, Polynomial.eval_map_algebraMap, aeval_algHom_apply]
    exact map_mem_span π (Fr ^ n) _ hpa
  obtain ⟨n₁, n₂, hne, heq⟩ := Finite.exists_ne_map_eq_of_infinite (fun n : ℕ => (⟨_, hroot n⟩ : ↥T))
  have heq' : Ideal.Quotient.mk I ((Fr ^ n₁) a) = Ideal.Quotient.mk I ((Fr ^ n₂) a) := congrArg Subtype.val heq

  wlog hlt : n₁ < n₂ generalizing n₁ n₂
  · exact this n₂ n₁ hne.symm heq.symm heq'.symm (lt_of_le_of_ne (not_lt.mp hlt) hne.symm)
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt hlt
  refine ⟨k + 1, Nat.succ_pos k, ?_⟩

  have h1 : (Fr ^ n₁) (a - (Fr ^ (k + 1)) a) ∈ I := by
    rw [map_sub, ← AlgEquiv.mul_apply, ← pow_add]
    exact (Ideal.Quotient.eq).mp heq'
  have h2 : a - (Fr ^ (k + 1)) a ∈ I := by
    have := map_mem_span π (Fr ^ n₁).symm _ h1
    rwa [AlgEquiv.symm_apply_apply] at this

  set Q : ℕ := r ^ (k + 1) with hQ
  have hQ2 : 2 ≤ Q := le_trans hr2 (Nat.le_self_pow (Nat.succ_ne_zero k) r)
  have hQI : ((Q : ℕ) : Onr) ∈ I := by
    rw [hQ, Nat.cast_pow]; exact I.pow_mem_of_mem hrI _ (Nat.succ_pos k)
  have haQ : a ^ Q - a ∈ I := by
    have h3 := frob_pow_sub_mem Fr r hFr (k + 1) a
    have e : a ^ Q - a = -((a - (Fr ^ (k + 1)) a) + ((Fr ^ (k + 1)) a - a ^ r ^ (k + 1))) := by rw [hQ]; ring
    rw [e]; exact I.neg_mem (I.add_mem h2 h3)
  obtain ⟨t, ht, hta⟩ := exists_teichmuller I Q hQ2 hQI a haQ
  refine ⟨t, ?_, ?_⟩
  · rw [frob_pow_teich hjac hFr Q hQI t ht, ← hQ, ht]
  · have : a - t = -(t - a) := by ring
    rw [this]; exact I.neg_mem hta

theorem exists_frob_pow_fixed_approx
    (hcomplete : IsAdicComplete (Ideal.span {algebraMap 𝒪 Onr π}) Onr)
    (hmax : (Ideal.span {algebraMap 𝒪 Onr π}).IsMaximal)
    (halg : ∀ x : Onr, ∃ p : Polynomial 𝒪, p.Monic ∧ Polynomial.aeval x p ∈ Ideal.span {algebraMap 𝒪 Onr π})
    (hFr : ∀ x : Onr, Fr x - x ^ r ∈ Ideal.span {algebraMap 𝒪 Onr π})
    (hr2 : 2 ≤ r) (hrI : ((r : ℕ) : Onr) ∈ Ideal.span {algebraMap 𝒪 Onr π}) (e : ℕ) :
    ∀ a : Onr, ∃ d : ℕ, 0 < d ∧ ∃ s w : Onr, (Fr ^ d) s = s ∧ a = s + algebraMap 𝒪 Onr π ^ e * w := by
  induction e with
  | zero =>
    intro a
    exact ⟨1, Nat.one_pos, 0, a, by rw [map_zero], by rw [pow_zero, one_mul, zero_add]⟩
  | succ e ih =>
    intro a
    obtain ⟨k, hk, t, ht, hat⟩ := exists_frob_pow_fixed_sub_mem hcomplete hmax halg hFr hr2 hrI a
    obtain ⟨a₁, ha₁⟩ := Ideal.mem_span_singleton'.mp hat
    obtain ⟨d, hd, s, w, hs, ha₁eq⟩ := ih a₁
    refine ⟨k * d, Nat.mul_pos hk hd, t + algebraMap 𝒪 Onr π * s, w, ?_, ?_⟩
    · have h1 : (Fr ^ (k * d)) t = t := by rw [pow_mul]; exact pow_apply_eq_self_of_apply_eq_self _ _ ht d
      have h2 : (Fr ^ (k * d)) s = s := by rw [mul_comm, pow_mul]; exact pow_apply_eq_self_of_apply_eq_self _ _ hs k
      rw [map_add, map_mul, AlgEquiv.commutes, h1, h2]
    · have : a = t + a₁ * algebraMap 𝒪 Onr π := by rw [ha₁]; ring
      rw [this, ha₁eq, pow_succ]; ring

theorem exists_teich_generator [IsDomain Onr] (Q : ℕ) (hQ : 2 ≤ Q) :
    ∃ ζ : Onr, ζ ^ Q = ζ ∧ ∀ t : Onr, t ^ Q = t → t = 0 ∨ ∃ n : ℕ, t = ζ ^ n := by
  classical

  let Tu : Subgroup Onrˣ :=
    { carrier := {u | ((u : Onrˣ) : Onr) ^ Q = u}
      one_mem' := by simp
      mul_mem' := by
        intro u v hu hv
        simp only [Set.mem_setOf_eq, Units.val_mul] at hu hv ⊢
        rw [mul_pow, hu, hv]
      inv_mem' := by
        intro u hu
        simp only [Set.mem_setOf_eq] at hu ⊢
        have hu' : u ^ Q = u := Units.ext (by rw [Units.val_pow_eq_pow_val]; exact hu)
        rw [← Units.val_pow_eq_pow_val, inv_pow, hu'] }

  have hX : ((X : Onr[X]) ^ Q - X) ≠ 0 := by
    apply Polynomial.Monic.ne_zero
    apply Polynomial.monic_X_pow_sub
    rw [degree_X]
    exact_mod_cast hQ
  have hfin : Set.Finite {t : Onr | t ^ Q = t} := by
    apply (((X : Onr[X]) ^ Q - X).roots.toFinset.finite_toSet).subset
    intro t ht
    simp only [Set.mem_setOf_eq] at ht
    rw [Finset.mem_coe, Multiset.mem_toFinset, mem_roots hX, IsRoot.def, eval_sub, eval_pow, eval_X, ht, sub_self]
  haveI : Finite {t : Onr // t ^ Q = t} := hfin.to_subtype
  haveI : Finite ↥Tu := Finite.of_injective (fun u : ↥Tu => (⟨((u : Onrˣ) : Onr), u.2⟩ : {t : Onr // t ^ Q = t}))
    (by
      intro u v h
      apply Subtype.ext
      apply Units.ext
      exact congrArg Subtype.val h)
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := ↥Tu)
  refine ⟨((g : Onrˣ) : Onr), g.2, ?_⟩
  intro t ht
  by_cases ht0 : t = 0
  · exact Or.inl ht0
  right
  have hQ1 : Q - 1 ≠ 0 := by omega
  have htu : IsUnit t := by
    apply IsUnit.of_pow_eq_one (n := Q - 1) _ hQ1
    apply mul_right_cancel₀ ht0
    rw [one_mul, ← pow_succ, Nat.sub_add_cancel (by omega), ht]
  set u : Onrˣ := htu.unit with hu
  have huT : u ∈ Tu := by
    show ((u : Onrˣ) : Onr) ^ Q = u
    rw [hu, IsUnit.unit_spec]; exact ht
  have hmem : (⟨u, huT⟩ : ↥Tu) ∈ Submonoid.powers g := mem_powers_iff_mem_zpowers.mpr (hg ⟨u, huT⟩)
  obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff _ _).mp hmem
  refine ⟨n, ?_⟩
  have := congrArg (fun x : ↥Tu => (((x : ↥Tu) : Onrˣ) : Onr)) hn
  simp only [SubgroupClass.coe_pow, Units.val_pow_eq_pow_val] at this
  rw [this, hu, IsUnit.unit_spec]

end Digits

section PiSep

theorem isCoprime_of_isUnit_sub {B : Type} [CommRing B] {a b : B} (h : IsUnit (a - b)) : IsCoprime a b := by
  obtain ⟨u, hu⟩ := h
  refine ⟨↑u⁻¹, -↑u⁻¹, ?_⟩
  have : (↑u⁻¹ : B) * a + -↑u⁻¹ * b = ↑u⁻¹ * (a - b) := by ring
  rw [this, ← hu, Units.inv_mul]

theorem nilpPoints_ext_of_quotients {𝒪 : Type} [CommRing 𝒪] {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of 𝒪))
    {B : Type} [CommRing B] [Algebra 𝒪 B] {ι : Type} [Fintype ι] (J : ι → Ideal B)
    (hJ : Pairwise fun i j => IsCoprime (J i) (J j)) (hinf : ⨅ i, J i = ⊥)
    (y₁ y₂ : (Scheme.nilpPoints f).obj B)
    (h : ∀ i, (Scheme.nilpPoints f).map (Ideal.Quotient.mkₐ 𝒪 (J i)) y₁ =
      (Scheme.nilpPoints f).map (Ideal.Quotient.mkₐ 𝒪 (J i)) y₂) :
    y₁ = y₂ := by
  classical

  set Φ : B →+* (∀ i, B ⧸ J i) := RingHom.pi (fun i => Ideal.Quotient.mk (J i)) with hΦ
  have hΦinj : Function.Injective Φ := by
    rw [injective_iff_map_eq_zero]
    intro b hb
    have hb' : b ∈ ⨅ i, J i := by
      rw [Ideal.mem_iInf]
      intro i
      exact Ideal.Quotient.eq_zero_iff_mem.mp (congr_fun hb i)
    rwa [hinf, Ideal.mem_bot] at hb'
  have hΦsurj : Function.Surjective Φ := by
    intro x
    obtain ⟨b, hb⟩ := Ideal.pi_quotient_surjective (fun i j hij => hJ hij) x
    exact ⟨b, funext hb⟩
  set eΦ : B ≃+* (∀ i, B ⧸ J i) := RingEquiv.ofBijective Φ ⟨hΦinj, hΦsurj⟩ with heΦ
  haveI : IsIso (CommRingCat.ofHom Φ) := by
    change IsIso eΦ.toCommRingCatIso.hom
    infer_instance
  apply Subtype.ext
  rw [← cancel_epi (Spec.map (CommRingCat.ofHom Φ)),
    ← cancel_epi (sigmaSpec (fun i => CommRingCat.of (B ⧸ J i)))]
  apply Limits.Sigma.hom_ext
  intro i
  rw [ι_sigmaSpec_assoc, ι_sigmaSpec_assoc, ← Spec.map_comp_assoc, ← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp]
  have hcomp : (Pi.evalRingHom (fun i => B ⧸ J i) i).comp Φ = (Ideal.Quotient.mkₐ 𝒪 (J i)).toRingHom := rfl
  have hi := congrArg Subtype.val (h i)
  simp only [Scheme.nilpPoints_map_val] at hi
  rw [hcomp]
  exact hi

end PiSep

section Frame

theorem isUnit_natCast_of_not_dvd {r : ℕ} [hr : Fact r.Prime]
    (𝒪 : Type) [CommRing 𝒪] [IsDomain 𝒪] (hdvr : IsDiscreteValuationRing 𝒪)
    (π : 𝒪) (hπ : Irreducible π) (hunr : Ideal.span {((r : ℕ) : 𝒪)} = Ideal.span {π})
    (m : ℕ) (hm : ¬ r ∣ m) : IsUnit ((m : ℕ) : 𝒪) := by
  by_contra hmu
  have hmax : IsLocalRing.maximalIdeal 𝒪 = Ideal.span {π} :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer π).mp hπ
  have hm_mem : ((m : ℕ) : 𝒪) ∈ Ideal.span {π} := hmax ▸ (mem_nonunits_iff.mpr hmu)
  have hr_mem : ((r : ℕ) : 𝒪) ∈ Ideal.span {π} := hunr ▸ Ideal.mem_span_singleton_self _
  have hcop : IsCoprime ((r : ℤ) : 𝒪) ((m : ℤ) : 𝒪) :=
    (Nat.isCoprime_iff_coprime.mpr ((Nat.Prime.coprime_iff_not_dvd hr.out).mpr hm)).map (Int.castRingHom 𝒪)
  simp only [Int.cast_natCast] at hcop
  obtain ⟨u, w, huw⟩ := hcop
  have h1 : (1 : 𝒪) ∈ Ideal.span {π} := huw ▸ Ideal.add_mem _ (Ideal.mul_mem_left _ _ hr_mem) (Ideal.mul_mem_left _ _ hm_mem)
  exact hπ.not_isUnit (Ideal.span_singleton_eq_top.mp ((Ideal.eq_top_iff_one _).mpr h1))

end Frame

theorem mem_inf_map_conj_of_central {a₁ b₁ : ℚ} (Γ : Subgroup (ℍ[ℚ, a₁, b₁])ˣ) (s z : (ℍ[ℚ, a₁, b₁])ˣ)
    (hz : z ∈ Γ) (hc : ∃ c : ℚ, (z : ℍ[ℚ, a₁, b₁]) = c • (1 : ℍ[ℚ, a₁, b₁])) :
    z ∈ Γ ⊓ Γ.map (MulAut.conj s).toMonoidHom := by
  refine Subgroup.mem_inf.mpr ⟨hz, Subgroup.mem_map.mpr ⟨z, hz, ?_⟩⟩
  obtain ⟨c, hc⟩ := hc
  show MulAut.conj s z = z
  rw [MulAut.conj_apply]
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, hc, mul_smul_comm, mul_one, smul_mul_assoc, Units.mul_inv]

end Q2CoeffT

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

    (hfMℓ : LocallyOfFiniteType fMℓ)
    :

    ∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π))
      (ψ ψ' : Onr →ₐ[𝒪] B) (P : (Omega K₀ π).obj B) (g : G),
      (∀ y : Onr, (∀ (z : (ℍ[ℚ, a₁, b₁])ˣ) (hz : z ∈ Γt), (∃ c : ℚ, (z : ℍ[ℚ, a₁, b₁]) = c • (1 : ℍ[ℚ, a₁, b₁])) →
              θt ⟨z, hz⟩ = 1 → (Fr ^ Multiplicative.toAdd (vdet ((Units.map (ι₀ : ℍ[ℚ, a₁, b₁] →* Matrix (Fin 2) (Fin 2) K₀)) z))) y = y) →
        ψ y = ψ' y) →
      Θfℓ B hB ((ψ, P), g) = Θfℓ B hB ((ψ', P), g) := by
  intro B _ _ hBπ ψ ψ' P gG hS
  classical
  haveI := hdvr
  have hrp : r.Prime := Fact.out

  set vz : (ℍ[ℚ, a₁, b₁])ˣ → ℤ :=
    fun z => Multiplicative.toAdd (vdet ((Units.map (ι₀ : ℍ[ℚ, a₁, b₁] →* Matrix (Fin 2) (Fin 2) K₀)) z)) with hvz
  set adm : (ℍ[ℚ, a₁, b₁])ˣ → Prop :=
    fun z => ∃ hz : z ∈ Γt, (∃ c : ℚ, (z : ℍ[ℚ, a₁, b₁]) = HSMul.hSMul c (1 : ℍ[ℚ, a₁, b₁])) ∧ θt ⟨z, hz⟩ = 1 with hadm
  have hadm_one : adm 1 := by
    refine ⟨Γt.one_mem, ⟨1, by rw [Units.val_one, one_smul]⟩, ?_⟩
    have : (⟨1, Γt.one_mem⟩ : ↥Γt) = 1 := rfl
    rw [this, map_one]
  have hadm_mul : ∀ z z', adm z → adm z' → adm (z * z') := by
    rintro z z' ⟨hz, ⟨c, hc⟩, hθ⟩ ⟨hz', ⟨c', hc'⟩, hθ'⟩
    refine ⟨Γt.mul_mem hz hz', ⟨c * c', ?_⟩, ?_⟩
    · rw [Units.val_mul, hc, hc', Algebra.smul_mul_assoc, one_mul, smul_smul]
    · have : (⟨z * z', Γt.mul_mem hz hz'⟩ : ↥Γt) = ⟨z, hz⟩ * ⟨z', hz'⟩ := rfl
      rw [this, map_mul, hθ, hθ', one_mul]
  have hadm_inv : ∀ z, adm z → adm z⁻¹ := by
    rintro z ⟨hz, ⟨c, hc⟩, hθ⟩
    have hc0 : c ≠ 0 := by
      intro h0
      apply Units.ne_zero z
      rw [hc, h0, zero_smul]
    refine ⟨Γt.inv_mem hz, ⟨c⁻¹, ?_⟩, ?_⟩
    · have h1 : (z : ℍ[ℚ, a₁, b₁]) * ↑z⁻¹ = 1 := Units.mul_inv z
      rw [hc, Algebra.smul_mul_assoc, one_mul] at h1
      have h2 := congrArg (fun x : ℍ[ℚ, a₁, b₁] => HSMul.hSMul c⁻¹ x) h1
      simp only [smul_smul, inv_mul_cancel₀ hc0, one_smul] at h2
      exact h2
    · have : (⟨z⁻¹, Γt.inv_mem hz⟩ : ↥Γt) = ⟨z, hz⟩⁻¹ := rfl
      rw [this, map_inv, hθ, inv_one]
  have hvz_one : vz 1 = 0 := by simp only [hvz, map_one, toAdd_one]
  have hvz_mul : ∀ z z', vz (z * z') = vz z + vz z' := fun z z' => by simp only [hvz, map_mul, toAdd_mul]
  have hvz_inv : ∀ z, vz z⁻¹ = - vz z := fun z => by simp only [hvz, map_inv, toAdd_inv]
  let V : AddSubgroup ℤ :=
    { carrier := {k | ∃ z, adm z ∧ vz z = k}
      zero_mem' := ⟨1, hadm_one, hvz_one⟩
      add_mem' := by
        rintro _ _ ⟨z, hz, rfl⟩ ⟨z', hz', rfl⟩
        exact ⟨z * z', hadm_mul z z' hz hz', hvz_mul z z'⟩
      neg_mem' := by
        rintro _ ⟨z, hz, rfl⟩
        exact ⟨z⁻¹, hadm_inv z hz, hvz_inv z⟩ }
  obtain ⟨a₀, ha₀⟩ := Int.subgroup_cyclic V
  set m : ℕ := a₀.natAbs with hmdef
  have hVdvd : ∀ k ∈ V, (m : ℤ) ∣ k := by
    intro k hk
    rw [ha₀, AddSubgroup.mem_closure_singleton] at hk
    obtain ⟨l, rfl⟩ := hk
    rw [hmdef, Int.natAbs_dvd, smul_eq_mul]
    exact Dvd.intro_left l rfl
  have hmV : (m : ℤ) ∈ V := by
    have ha₀V : a₀ ∈ V := by rw [ha₀]; exact AddSubgroup.subset_closure (Set.mem_singleton a₀)
    rcases Int.natAbs_eq a₀ with h | h
    · rw [hmdef, ← h]; exact ha₀V
    · rw [hmdef, show ((a₀.natAbs : ℕ) : ℤ) = -a₀ by omega]; exact V.neg_mem ha₀V

  have hSψ : ∀ y : Onr, (Fr ^ m) y = y → ψ y = ψ' y := by
    intro y hy
    apply hS y
    intro z hz hcz hθz
    have hk : vz z ∈ V := ⟨z, ⟨hz, hcz, hθz⟩, rfl⟩
    obtain ⟨l, hl⟩ := hVdvd _ hk
    show (Fr ^ vz z) y = y
    rw [hl, zpow_mul, zpow_natCast]
    exact Q2CoeffT.zpow_apply_eq_self_of_apply_eq_self (Fr ^ m) y hy l

  rcases Nat.eq_zero_or_pos m with hm0 | hm
  · have hψψ' : ψ = ψ' := AlgHom.ext fun y => hSψ y (by rw [hm0, pow_zero, AlgEquiv.one_apply])
    rw [hψψ']

  obtain ⟨u, hu⟩ := (Ideal.span_singleton_eq_span_singleton.mp hunr : Associated ((r : ℕ) : 𝒪) π)
  have hr𝒪 : ((r : ℕ) : 𝒪) = π * (↑u⁻¹ : 𝒪) := by rw [← hu, mul_assoc, Units.mul_inv, mul_one]
  set ϖ : Onr := algebraMap 𝒪 Onr π with hϖ
  have hrI : ((r : ℕ) : Onr) ∈ Ideal.span {ϖ} := by
    rw [← map_natCast (algebraMap 𝒪 Onr), hr𝒪, map_mul]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
  have hϖ0 : ϖ ≠ 0 := by
    intro h0
    apply hrp.ne_zero
    have : ((r : ℕ) : Onr) = 0 := by
      rw [← map_natCast (algebraMap 𝒪 Onr), hr𝒪, map_mul, ← hϖ, h0, zero_mul]
    exact_mod_cast this
  haveI := hOnr_complete
  have hjac : Ideal.span {ϖ} ≤ Ideal.jacobson ⊥ := IsAdicComplete.le_jacobson_bot _
  have hr2 : 2 ≤ r := hrp.two_le
  obtain ⟨e, he⟩ := id hBπ

  set C : Type := Onr ⊗[𝒪] B with hCdef
  set incl : Onr →ₐ[𝒪] C := (Algebra.TensorProduct.includeLeft : Onr →ₐ[𝒪] C) with hincl
  set jB : B →ₐ[𝒪] C := (Algebra.TensorProduct.includeRight : B →ₐ[𝒪] C) with hjB
  have hCπ : IsNilpotent (algebraMap 𝒪 C π) := ⟨e, by rw [← jB.commutes, ← map_pow, he, map_zero]⟩
  set PC : (Omega K₀ π).obj C := (Omega K₀ π).map jB P with hPC
  set Y : (Scheme.nilpPoints fMℓ).obj C := Θfℓ C hCπ ((incl, PC), gG) with hY

  set τ : ℤ → (C →ₐ[𝒪] C) :=
    fun k => Algebra.TensorProduct.map ((Fr ^ k : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 B) with hτ
  have hτ_tmul : ∀ (k : ℤ) (y : Onr) (b : B), τ k (y ⊗ₜ[𝒪] b) = (Fr ^ k) y ⊗ₜ[𝒪] b := fun k y b => rfl
  have hτ_incl : ∀ k : ℤ, (τ k).comp incl = incl.comp ((Fr ^ k : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) :=
    fun k => AlgHom.ext fun y => hτ_tmul k y 1
  have hτ_j : ∀ k : ℤ, (τ k).comp jB = jB := fun k => AlgHom.ext fun b => by
    show τ k ((1 : Onr) ⊗ₜ[𝒪] b) = (1 : Onr) ⊗ₜ[𝒪] b
    rw [hτ_tmul, map_one]
  have hτPC : ∀ k : ℤ, (Omega K₀ π).map (τ k) PC = PC := fun k => by
    rw [hPC, ← (Omega K₀ π).map_comp, hτ_j]

  have hYinv : ∀ k ∈ V, (Scheme.nilpPoints fMℓ).map (τ k) Y = Y := by
    intro k hk
    obtain ⟨z, ⟨hz, ⟨c, hc⟩, hθ⟩, hzk⟩ := V.neg_mem hk
    have hc0 : c ≠ 0 := by
      intro h0
      apply Units.ne_zero z
      rw [hc, h0, zero_smul]
    set c' : K₀ˣ := Units.mk0 (algebraMap ℚ K₀ c) ((map_ne_zero (algebraMap ℚ K₀)).mpr hc0) with hc'
    have hgz : (Units.map (ι₀ : ℍ[ℚ, a₁, b₁] →* Matrix (Fin 2) (Fin 2) K₀)) z = scalarGL c' := by
      apply Units.ext
      rw [Units.coe_map, MonoidHom.coe_coe, scalarGL_coe, hc, map_smul, map_one, hc', Units.val_mk0, algebraMap_smul]
    have hpull : DeligneDatum.IsPullback (K := K₀) (π := π) C
        ((Units.map (ι₀ : ℍ[ℚ, a₁, b₁] →* Matrix (Fin 2) (Fin 2) K₀)) z)⁻¹ PC PC := by
      have h1 := CerednikDrinfeld.FormalOmega.Omega.action_scalarGL (K := K₀) π C c' PC
      change DeligneDatum.pullback π C (scalarGL c')⁻¹ PC = PC at h1
      have h2 := DeligneDatum.isPullback_pullback π C (scalarGL c')⁻¹ PC
      rw [h1] at h2
      rw [hgz]
      exact h2
    have h3 := hinvℓ C hCπ z hz (by rw [hΓtℓ ℓ]; exact Q2CoeffT.mem_inf_map_conj_of_central Γt (s ℓ) z hz ⟨c, hc⟩) (incl, PC) (frobTwist Onr Fr (- vz z) incl, PC) gG ⟨rfl, hpull⟩
    rw [hθ, one_mul, ← hY] at h3
    have h4 := hnatℓ C C hCπ hCπ (τ k) ((incl, PC), gG)
    have h5 : (AlgFunctor.prod (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)) (AlgFunctor.const G)).map (τ k)
        ((incl, PC), gG) = ((frobTwist Onr Fr (- vz z) incl, PC), gG) := by
      show ((((τ k).comp incl, (Omega K₀ π).map (τ k) PC), gG) :
          (AlgFunctor.prod (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)) (AlgFunctor.const G)).obj C) =
        ((incl.comp ((Fr ^ (- vz z) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr), PC), gG)
      rw [hτ_incl, hτPC, show - vz z = k by omega]
      rfl
    have h6 : Θfℓ C hCπ ((AlgFunctor.prod (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)) (AlgFunctor.const G)).map (τ k)
        ((incl, PC), gG)) = Y := by
      rw [h5]
      exact h3
    exact h4.symm.trans h6
  have hYinv_nat : ∀ i : ℕ, (Scheme.nilpPoints fMℓ).map (τ ((m * i : ℕ) : ℤ)) Y = Y := by
    intro i
    apply hYinv
    have := V.zsmul_mem hmV (i : ℤ)
    rwa [smul_eq_mul, show (i : ℤ) * (m : ℤ) = ((m * i : ℕ) : ℤ) by push_cast; ring] at this

  set φ_ : (Onr →ₐ[𝒪] B) → (C →ₐ[𝒪] B) :=
    fun ξ => Algebra.TensorProduct.lift ξ (AlgHom.id 𝒪 B) (fun _ _ => Commute.all _ _) with hφ_
  have hφ_tmul : ∀ (ξ : Onr →ₐ[𝒪] B) (y : Onr) (b : B), φ_ ξ (y ⊗ₜ[𝒪] b) = ξ y * b := fun ξ y b => rfl
  have hΘY : ∀ ξ : Onr →ₐ[𝒪] B, Θfℓ B hBπ ((ξ, P), gG) = (Scheme.nilpPoints fMℓ).map (φ_ ξ) Y := by
    intro ξ
    have h1 := hnatℓ C B hCπ hBπ (φ_ ξ) ((incl, PC), gG)
    have e1 : (φ_ ξ).comp incl = ξ := AlgHom.ext fun y => by
      show φ_ ξ (y ⊗ₜ[𝒪] (1 : B)) = ξ y
      rw [hφ_tmul, mul_one]
    have e2 : (φ_ ξ).comp jB = AlgHom.id 𝒪 B := AlgHom.ext fun b => by
      show φ_ ξ ((1 : Onr) ⊗ₜ[𝒪] b) = b
      rw [hφ_tmul, map_one, one_mul]
    have h2 : (AlgFunctor.prod (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)) (AlgFunctor.const G)).map (φ_ ξ)
        ((incl, PC), gG) = ((ξ, P), gG) := by
      show ((((φ_ ξ).comp incl, (Omega K₀ π).map (φ_ ξ) PC), gG) :
          (AlgFunctor.prod (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)) (AlgFunctor.const G)).obj B) = ((ξ, P), gG)
      rw [e1, hPC, ← (Omega K₀ π).map_comp, e2, (Omega K₀ π).map_id]
      rfl
    rw [h2, ← hY] at h1
    exact h1

  haveI : LocallyOfFiniteType fMℓ := hfMℓ
  obtain ⟨S, hSfg, Y₀, hY₀⟩ :=
    (AlgebraicGeometry.Scheme.nilpPoints.exists_subalgebra_fg_map_eq_of_locallyOfFiniteType 𝒪 fMℓ).1 C Y
  set ιS : ↥S →ₐ[𝒪] C := (S.val).restrictScalars 𝒪 with hιS

  set Cd : ℕ → Subalgebra 𝒪 C :=
    fun d => Algebra.adjoin 𝒪 {x : C | ∃ t : Onr, (Fr ^ (m * d)) t = t ∧ ∃ b : B, x = t ⊗ₜ[𝒪] b} with hCd
  have hCd_mono : ∀ d d' : ℕ, d ∣ d' → Cd d ≤ Cd d' := by
    rintro d d' ⟨k, rfl⟩
    apply Algebra.adjoin_mono
    rintro x ⟨t, ht, b, rfl⟩
    refine ⟨t, ?_, b, rfl⟩
    rw [← mul_assoc, pow_mul]
    exact Q2CoeffT.pow_apply_eq_self_of_apply_eq_self _ _ ht k
  have hmemCd : ∀ x : C, ∃ d : ℕ, 0 < d ∧ x ∈ Cd d := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => exact ⟨1, Nat.one_pos, zero_mem _⟩
    | tmul a b =>
      obtain ⟨d, hd, sa, w, hsa, ha⟩ :=
        Q2CoeffT.exists_frob_pow_fixed_approx hOnr_complete hOnr_max hOnr_alg hFr hr2 hrI e a
      refine ⟨d, hd, Algebra.subset_adjoin ⟨sa, ?_, b, ?_⟩⟩
      · rw [mul_comm, pow_mul]
        exact Q2CoeffT.pow_apply_eq_self_of_apply_eq_self _ _ hsa m
      · have h0 : (ϖ ^ e * w) ⊗ₜ[𝒪] b = 0 := by
          rw [hϖ, ← map_pow, ← Algebra.smul_def, TensorProduct.smul_tmul, Algebra.smul_def, map_pow, he, zero_mul,
            TensorProduct.tmul_zero]
        rw [ha, TensorProduct.add_tmul, h0, add_zero]
    | add x y hx hy =>
      obtain ⟨dx, hdx, hx⟩ := hx
      obtain ⟨dy, hdy, hy⟩ := hy
      exact ⟨dx * dy, Nat.mul_pos hdx hdy,
        add_mem (hCd_mono _ _ (dvd_mul_right dx dy) hx) (hCd_mono _ _ (dvd_mul_left dy dx) hy)⟩
  obtain ⟨t₀, ht₀⟩ := hSfg
  choose dOf hdOf_pos hdOf_mem using hmemCd
  set d : ℕ := ∏ x ∈ t₀, dOf x with hd
  have hdpos : 0 < d := Finset.prod_pos fun x _ => hdOf_pos x
  have hSle : S ≤ Cd d := by
    rw [← ht₀]
    apply Algebra.adjoin_le
    intro x hx
    exact hCd_mono _ _ (Finset.dvd_prod_of_mem _ (Finset.mem_coe.mp hx)) (hdOf_mem x)

  set Q : ℕ := r ^ (m * d) with hQ
  have hmd : 0 < m * d := Nat.mul_pos hm hdpos
  have hQ2 : 2 ≤ Q := le_trans hr2 (Nat.le_self_pow hmd.ne' r)
  have hQI : ((Q : ℕ) : Onr) ∈ Ideal.span {ϖ} := by
    rw [hQ, Nat.cast_pow]; exact Ideal.pow_mem_of_mem _ hrI _ hmd
  have hσq : ∀ y : Onr, (Fr ^ (m * d)) y - y ^ Q ∈ Ideal.span {ϖ} := fun y => Q2CoeffT.frob_pow_sub_mem Fr r hFr (m * d) y
  obtain ⟨ζ, hζQ, hζgen⟩ := Q2CoeffT.exists_teich_generator (Onr := Onr) Q hQ2
  have hFrζ : ∀ k : ℕ, (Fr ^ k) ζ = ζ ^ r ^ k := Q2CoeffT.frob_pow_teich hjac hFr Q hQI ζ hζQ
  have hζteich : ∀ k : ℕ, ((Fr ^ k) ζ) ^ Q = (Fr ^ k) ζ := fun k => by rw [← map_pow, hζQ]
  have hζfix : (Fr ^ (m * d)) ζ = ζ := by rw [hFrζ, ← hQ, hζQ]
  have hex : ∃ k : ℕ, 0 < k ∧ (Fr ^ (m * k)) ζ = ζ := ⟨d, hdpos, hζfix⟩
  set d' : ℕ := Nat.find hex with hd'
  have hd'pos : 0 < d' := (Nat.find_spec hex).1
  have hd'fix : (Fr ^ (m * d')) ζ = ζ := (Nat.find_spec hex).2
  have hd'min : ∀ k : ℕ, 0 < k → k < d' → (Fr ^ (m * k)) ζ ≠ ζ := fun k hk hlt h => Nat.find_min hex hlt ⟨hk, h⟩
  have hdist : ∀ i j : ℕ, i < d' → j < d' → i ≠ j → (Fr ^ (m * i)) ζ ≠ (Fr ^ (m * j)) ζ := by
    intro i j hi hj hij h
    wlog hlt : i < j generalizing i j
    · exact this j i hj hi (Ne.symm hij) h.symm (lt_of_le_of_ne (not_lt.mp hlt) (Ne.symm hij))
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt hlt
    apply hd'min (k + 1) (Nat.succ_pos k) (by omega)
    apply (Fr ^ (m * i)).injective
    rw [← AlgEquiv.mul_apply, ← pow_add, show m * i + m * (k + 1) = m * (i + k + 1) by ring]
    exact h.symm

  set c : ℕ → B := fun i => ψ ((Fr ^ (m * i)) ζ) with hc
  set t' : B := ψ' ζ with ht'
  have hcu : ∀ i j : ℕ, i < d' → j < d' → i ≠ j → IsUnit (c i - c j) := by
    intro i j hi hj hij
    have := (Q2CoeffT.isUnit_sub_of_pow_eq (Ideal.span {ϖ}) hOnr_max hjac Q hQI _ _ (hζteich (m * i)) (hζteich (m * j))
      (hdist i j hi hj hij)).map ψ
    rwa [map_sub] at this
  have hprod : ∏ i ∈ Finset.range d', (t' - c i) = 0 := by
    set F : ℕ → Polynomial Onr := fun i => Polynomial.X - Polynomial.C ((Fr ^ (m * i)) ζ) with hF
    set gp : Polynomial Onr := ∏ i ∈ Finset.range d', F i with hgp
    have hFmap : ∀ i : ℕ, (F i).map ((Fr ^ m : Onr ≃ₐ[𝒪] Onr) : Onr →+* Onr) = F (i + 1) := by
      intro i
      rw [hF]
      simp only [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, RingHom.coe_coe]
      congr 2
      rw [← AlgEquiv.mul_apply, ← pow_add, show m + m * i = m * (i + 1) by ring]
    have hFd' : F d' = F 0 := by
      show Polynomial.X - Polynomial.C ((Fr ^ (m * d')) ζ) = Polynomial.X - Polynomial.C ((Fr ^ (m * 0)) ζ)
      rw [hd'fix, mul_zero, pow_zero, AlgEquiv.one_apply]
    have hgpmap : gp.map ((Fr ^ m : Onr ≃ₐ[𝒪] Onr) : Onr →+* Onr) = gp := by
      rw [hgp, Polynomial.map_prod]
      simp only [hFmap]
      have h1 := Finset.prod_range_succ' F d'
      have h2 := Finset.prod_range_succ F d'
      rw [hFd'] at h2
      have hF0 : F 0 ≠ 0 := Polynomial.X_sub_C_ne_zero _
      exact mul_right_cancel₀ hF0 (h1.symm.trans h2)
    have hcoef : ∀ k : ℕ, (Fr ^ m) (gp.coeff k) = gp.coeff k := fun k => by
      conv_rhs => rw [← hgpmap, Polynomial.coeff_map]
      rfl
    have hmapeq : gp.map (ψ : Onr →+* B) = gp.map (ψ' : Onr →+* B) := by
      ext k
      rw [Polynomial.coeff_map, Polynomial.coeff_map]
      exact hSψ _ (hcoef k)
    have hev0 : gp.eval ζ = 0 := by
      rw [hgp, Polynomial.eval_prod]
      apply Finset.prod_eq_zero (Finset.mem_range.mpr hd'pos)
      show Polynomial.eval ζ (Polynomial.X - Polynomial.C ((Fr ^ (m * 0)) ζ)) = 0
      rw [mul_zero, pow_zero, AlgEquiv.one_apply, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, sub_self]
    have hev1 : (gp.map (ψ' : Onr →+* B)).eval t' = 0 := by
      rw [ht', Polynomial.eval_map, ← RingHom.coe_coe, Polynomial.eval₂_at_apply, hev0, map_zero]
    rw [← hmapeq, hgp, Polynomial.map_prod, Polynomial.eval_prod] at hev1
    rw [← hev1]
    apply Finset.prod_congr rfl
    intro i _
    rw [hF]
    simp only [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, Polynomial.eval_sub, Polynomial.eval_X,
      Polynomial.eval_C, RingHom.coe_coe]
    rfl

  have hcopel : ∀ i j : Fin d', i ≠ j → IsCoprime (t' - c i) (t' - c j) := by
    intro i j hij
    apply Q2CoeffT.isCoprime_of_isUnit_sub
    have e1 : t' - c i - (t' - c j) = c j - c i := by ring
    rw [e1]
    exact hcu j i j.2 i.2 (fun h => hij (Fin.ext h.symm))
  set J : Fin d' → Ideal B := fun i => Ideal.span {t' - c i} with hJ
  have hJcop : Pairwise fun i j => IsCoprime (J i) (J j) := by
    intro i j hij
    show IsCoprime (Ideal.span {t' - c i}) (Ideal.span {t' - c j})
    rw [Ideal.isCoprime_span_singleton_iff]
    exact hcopel i j hij
  have hJinf : ⨅ i, J i = ⊥ := by
    show ⨅ i : Fin d', Ideal.span {t' - c i} = ⊥
    rw [Ideal.iInf_span_singleton hcopel, ← Finset.prod_range (fun i => t' - c i), hprod, Ideal.span_singleton_eq_bot]
  set pq : ∀ i : Fin d', B →ₐ[𝒪] B ⧸ J i := fun i => Ideal.Quotient.mkₐ 𝒪 (J i) with hpq
  have hpq_base : ∀ i : Fin d', pq i t' = pq i (c i) := fun i => by
    show Ideal.Quotient.mkₐ 𝒪 (J i) t' = Ideal.Quotient.mkₐ 𝒪 (J i) (c i)
    rw [Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq]
    exact Ideal.mem_span_singleton_self _

  have hkeyT : ∀ (i : Fin d') (t : Onr), t ^ Q = t → pq i (ψ' t) = pq i (ψ ((Fr ^ (m * (i : ℕ))) t)) := by
    intro i t ht
    rcases hζgen t ht with rfl | ⟨k, rfl⟩
    · simp only [map_zero]
    · rw [map_pow, map_pow, map_pow, map_pow, map_pow]
      show (pq i t') ^ k = (pq i (c i)) ^ k
      rw [hpq_base]

  have hkey : ∀ (i : Fin d') (y : Onr), (Fr ^ (m * d)) y = y → pq i (ψ' y) = pq i (ψ ((Fr ^ (m * (i : ℕ))) y)) := by
    intro i y hy
    have hyfix : y ∈ Q2CoeffT.Fix ({Fr ^ (m * d)} : Set (Onr ≃ₐ[𝒪] Onr)) := by
      intro σ hσ
      rw [Set.mem_singleton_iff.mp hσ]
      exact hy
    obtain ⟨ts, y', hts, hyeq⟩ := Q2CoeffT.exists_digits (Fam := ({Fr ^ (m * d)} : Set (Onr ≃ₐ[𝒪] Onr))) hOnr_complete
      hQ2 hQI hϖ0 (Fr ^ (m * d)) (Set.mem_singleton _) hσq e y hyfix
    rw [hyeq, Q2CoeffT.apply_digits ψ' (pq i) he, Q2CoeffT.algEquiv_digits, Q2CoeffT.apply_digits ψ (pq i) he]
    apply Finset.sum_congr rfl
    intro j _
    rw [hkeyT i (ts j) (hts j).1]

  have hagree : ∀ (i : Fin d') (x : C), x ∈ Cd d →
      pq i (φ_ ψ' x) = pq i (φ_ ψ (τ ((m * (i : ℕ) : ℕ) : ℤ) x)) := by
    intro i x hx
    have hle : Cd d ≤ AlgHom.equalizer ((pq i).comp (φ_ ψ')) ((pq i).comp ((φ_ ψ).comp (τ ((m * (i : ℕ) : ℕ) : ℤ)))) := by
      apply Algebra.adjoin_le
      rintro x ⟨t, ht, b, rfl⟩
      show pq i (φ_ ψ' (t ⊗ₜ[𝒪] b)) = pq i (φ_ ψ (τ ((m * (i : ℕ) : ℕ) : ℤ) (t ⊗ₜ[𝒪] b)))
      rw [hτ_tmul, hφ_tmul, hφ_tmul, map_mul, map_mul, zpow_natCast, hkey i t ht]
    exact hle hx

  have hfinal : ∀ i : Fin d', (Scheme.nilpPoints fMℓ).map (pq i) (Θfℓ B hBπ ((ψ, P), gG)) =
      (Scheme.nilpPoints fMℓ).map (pq i) (Θfℓ B hBπ ((ψ', P), gG)) := by
    intro i
    have hA : (pq i).comp ((φ_ ψ').comp ιS) = (pq i).comp ((φ_ ψ).comp ((τ ((m * (i : ℕ) : ℕ) : ℤ)).comp ιS)) :=
      AlgHom.ext fun x => hagree i (x : C) (hSle x.2)
    rw [hΘY ψ, hΘY ψ']
    symm
    calc (Scheme.nilpPoints fMℓ).map (pq i) ((Scheme.nilpPoints fMℓ).map (φ_ ψ') Y)
        = (Scheme.nilpPoints fMℓ).map (pq i) ((Scheme.nilpPoints fMℓ).map (φ_ ψ') ((Scheme.nilpPoints fMℓ).map ιS Y₀)) := by
          rw [hY₀]
      _ = (Scheme.nilpPoints fMℓ).map ((pq i).comp ((φ_ ψ').comp ιS)) Y₀ := by
          rw [(Scheme.nilpPoints fMℓ).map_comp, (Scheme.nilpPoints fMℓ).map_comp]
      _ = (Scheme.nilpPoints fMℓ).map ((pq i).comp ((φ_ ψ).comp ((τ ((m * (i : ℕ) : ℕ) : ℤ)).comp ιS))) Y₀ := by rw [hA]
      _ = (Scheme.nilpPoints fMℓ).map (pq i) ((Scheme.nilpPoints fMℓ).map (φ_ ψ)
            ((Scheme.nilpPoints fMℓ).map (τ ((m * (i : ℕ) : ℕ) : ℤ)) ((Scheme.nilpPoints fMℓ).map ιS Y₀))) := by
          rw [(Scheme.nilpPoints fMℓ).map_comp, (Scheme.nilpPoints fMℓ).map_comp, (Scheme.nilpPoints fMℓ).map_comp]
      _ = (Scheme.nilpPoints fMℓ).map (pq i) ((Scheme.nilpPoints fMℓ).map (φ_ ψ) Y) := by
          rw [hY₀, hYinv_nat]
  exact Q2CoeffT.nilpPoints_ext_of_quotients fMℓ J hJcop hJinf _ _ hfinal

end S_CerednikDrinfeld_QM_IsFineModuliT_cerednikDrinfeld_uniformization_fine_eq_of_forall_frobFixed_eq
end P2MW
export P2MW.S_CerednikDrinfeld_QM_IsFineModuliT_cerednikDrinfeld_uniformization_fine_eq_of_forall_frobFixed_eq (solution)
