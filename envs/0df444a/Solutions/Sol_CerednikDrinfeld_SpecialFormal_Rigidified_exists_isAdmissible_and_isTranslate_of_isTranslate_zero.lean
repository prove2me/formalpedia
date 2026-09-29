-- Prove2me | solution 1 for CerednikDrinfeld.SpecialFormal.Rigidified.exists_isAdmissible_and_isTranslate_of_isTranslate_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/6bcb6102-eda7-5fe5-8711-7920211717a8

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_SpecialFormalFunctorG
import Theorems.Thm_WittVector_ringHom_map_frobenius_of_finite
import Theorems.Thm_CerednikDrinfeld_FormalODModule_HasKernelOfDegree_comp_X_pow
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_SpecialFormal_Rigidified_exists_isAdmissible_and_isTranslate_of_isTranslate_zero

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

noncomputable section

namespace R4TranslateExists

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal
open MvPowerSeries (subst HasSubst hasSubst_of_constantCoeff_zero constantCoeff coeff subst_X coe_substAlgHom)

universe u v

section SeriesAlgebra

variable {A : Type u} [CommRing A]

def powPair (A : Type u) [CommRing A] (q : ℕ) : Series A :=
  fun i => (MvPowerSeries.X i : MvPowerSeries (Fin 2) A) ^ q

theorem constantCoeff_powPair {q : ℕ} (hq : q ≠ 0) (i : Fin 2) : constantCoeff (powPair A q i) = 0 := by
  rw [powPair, map_pow, MvPowerSeries.constantCoeff_X, zero_pow hq]

theorem hasSubst_powPair {q : ℕ} (hq : q ≠ 0) : HasSubst (powPair A q) :=
  hasSubst_of_constantCoeff_zero (constantCoeff_powPair hq)

theorem powPair_comp (q : ℕ) (φ : Series A) (hφ : ∀ i, constantCoeff (φ i) = 0) :
    (powPair A q).comp φ = fun i => φ i ^ q := by
  funext i
  show subst φ ((MvPowerSeries.X i : MvPowerSeries (Fin 2) A) ^ q) = φ i ^ q
  rw [← coe_substAlgHom (hasSubst_of_constantCoeff_zero hφ), map_pow, coe_substAlgHom,
    subst_X (hasSubst_of_constantCoeff_zero hφ)]

theorem powPair_comp_powPair {q q' : ℕ} (hq' : q' ≠ 0) :
    (powPair A q).comp (powPair A q') = powPair A (q' * q) := by
  rw [powPair_comp q _ (constantCoeff_powPair hq')]
  funext i
  rw [powPair, powPair, pow_mul]

theorem prod_powPair_pow (q : ℕ) (d : Fin 2 →₀ ℕ) :
    (d.prod fun s n => powPair A q s ^ n) = MvPowerSeries.monomial (q • d) (1 : A) := by
  rw [Finsupp.prod_fintype _ _ (fun i => pow_zero _)]
  have h : ∀ i : Fin 2, powPair A q i ^ d i = MvPowerSeries.monomial (Finsupp.single i ((q • d) i)) (1 : A) := by
    intro i
    rw [powPair, ← pow_mul, MvPowerSeries.X_pow_eq, Finsupp.smul_apply, smul_eq_mul]
  simp_rw [h]
  rw [MvPowerSeries.prod_monomial, Finset.prod_const_one, Finsupp.univ_sum_single]

theorem smul_finsupp_injective {q : ℕ} (hq : q ≠ 0) {d d' : Fin 2 →₀ ℕ} (h : q • d = q • d') : d = d' := by
  ext i
  have := DFunLike.congr_fun h i
  simp only [Finsupp.smul_apply, smul_eq_mul] at this
  exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hq) this

theorem coeff_smul_subst_powPair {q : ℕ} (hq : q ≠ 0) (f : MvPowerSeries (Fin 2) A) (m : Fin 2 →₀ ℕ) :
    coeff (q • m) (subst (powPair A q) f) = coeff m f := by
  classical
  rw [MvPowerSeries.coeff_subst (hasSubst_powPair hq)]
  have h : ∀ d : Fin 2 →₀ ℕ,
      coeff d f • coeff (q • m) (d.prod fun s n => powPair A q s ^ n) = if d = m then coeff m f else 0 := by
    intro d
    rw [prod_powPair_pow, MvPowerSeries.coeff_monomial]
    by_cases hd : d = m
    · subst hd; simp
    · have hne : q • m ≠ q • d := fun h' => hd (smul_finsupp_injective hq h').symm
      rw [if_neg hne, if_neg hd, smul_zero]
  simp_rw [h]
  rw [finsum_eq_single _ m (fun d hd => if_neg hd), if_pos rfl]

theorem comp_powPair_injective {q : ℕ} (hq : q ≠ 0) {φ ψ : Series A}
    (h : φ.comp (powPair A q) = ψ.comp (powPair A q)) : φ = ψ := by
  funext i
  ext m
  have hi := congrFun h i
  change subst (powPair A q) (φ i) = subst (powPair A q) (ψ i) at hi
  rw [← coeff_smul_subst_powPair hq (φ i) m, ← coeff_smul_subst_powPair hq (ψ i) m, hi]

variable {p : ℕ} [Fact p.Prime]

theorem frobSeries_eq_powPair (j : ℕ) : Rigidified.frobSeries (p := p) A j = powPair A (p ^ j) := rfl

theorem ppow_ne_zero (j : ℕ) : p ^ j ≠ 0 := pow_ne_zero _ (Fact.out : p.Prime).ne_zero

theorem constantCoeff_frobSeries (j : ℕ) (i : Fin 2) :
    constantCoeff (Rigidified.frobSeries (p := p) A j i) = 0 :=
  constantCoeff_powPair (ppow_ne_zero j) i

theorem frobSeries_comp_frobSeries (a b : ℕ) :
    (Rigidified.frobSeries (p := p) A a).comp (Rigidified.frobSeries (p := p) A b) =
      Rigidified.frobSeries (p := p) A (a + b) := by
  rw [frobSeries_eq_powPair, frobSeries_eq_powPair, frobSeries_eq_powPair,
    powPair_comp_powPair (ppow_ne_zero b), ← pow_add, add_comm]

theorem comp_frobSeries_injective (j : ℕ) {φ ψ : Series A}
    (h : φ.comp (Rigidified.frobSeries (p := p) A j) = ψ.comp (Rigidified.frobSeries (p := p) A j)) : φ = ψ :=
  comp_powPair_injective (ppow_ne_zero j) h

theorem frobSeries_zero : Rigidified.frobSeries (p := p) A 0 = Series.id A := by
  funext i
  simp only [Rigidified.frobSeries, pow_zero, pow_one, Series.id]

end SeriesAlgebra

section ActAlgebra

variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] (Y : FormalODModule p A)

def sm (i : ℕ) (φ : Series A) : Series A := (Y.act ((p : Zp2 p) ^ i)).comp φ

theorem constantCoeff_act (a : Zp2 p) (i : Fin 2) : constantCoeff (Y.act a i) = 0 := (Y.isLawHom_act a).1 i

theorem constantCoeff_sm (i : ℕ) (φ : Series A) (hφ : ∀ l, constantCoeff (φ l) = 0) (l : Fin 2) :
    constantCoeff (sm Y i φ l) = 0 :=
  Series.constantCoeff_comp (constantCoeff_act Y _) hφ l

theorem sm_sm (i j : ℕ) (φ : Series A) (hφ : ∀ l, constantCoeff (φ l) = 0) :
    sm Y i (sm Y j φ) = sm Y (i + j) φ := by
  rw [sm, sm, sm, ← Series.comp_assoc _ _ _ (constantCoeff_act Y _) hφ, ← FormalODModule.act_pow_add]

theorem sm_comm (i j : ℕ) (φ : Series A) (hφ : ∀ l, constantCoeff (φ l) = 0) :
    sm Y i (sm Y j φ) = sm Y j (sm Y i φ) := by
  rw [sm_sm Y i j φ hφ, sm_sm Y j i φ hφ, add_comm]

theorem sm_comp (i : ℕ) (φ ψ : Series A) (hφ : ∀ l, constantCoeff (φ l) = 0) (hψ : ∀ l, constantCoeff (ψ l) = 0) :
    (sm Y i φ).comp ψ = sm Y i (φ.comp ψ) :=
  Series.comp_assoc _ _ _ hφ hψ

theorem sm_zero (φ : Series A) (hφ : ∀ l, constantCoeff (φ l) = 0) : sm Y 0 φ = φ := by
  rw [sm, pow_zero, Y.act_one, Series.id_comp _ hφ]

theorem sm_comp_frob_cancel (i i' : ℕ) (φ ψ : Series A) (hφ : ∀ l, constantCoeff (φ l) = 0)
    (hψ : ∀ l, constantCoeff (ψ l) = 0) (j : ℕ)
    (h : sm Y i (φ.comp (Rigidified.frobSeries (p := p) A j)) = sm Y i' (ψ.comp (Rigidified.frobSeries (p := p) A j))) :
    sm Y i φ = sm Y i' ψ := by
  rw [← sm_comp Y i φ _ hφ (constantCoeff_frobSeries j), ← sm_comp Y i' ψ _ hψ (constantCoeff_frobSeries j)] at h
  exact comp_frobSeries_injective j h

end ActAlgebra

section Key

variable {σ : Type u} [Fintype σ] [DecidableEq σ] {A : Type v} [CommRing A]

def xpow (σ : Type u) (A : Type v) [CommRing A] (q : ℕ) : σ → MvPowerSeries σ A :=
  fun s => (MvPowerSeries.X s : MvPowerSeries σ A) ^ q

theorem constantCoeff_xpow {q : ℕ} (hq : q ≠ 0) (s : σ) : constantCoeff (xpow σ A q s) = 0 := by
  rw [xpow, map_pow, MvPowerSeries.constantCoeff_X, zero_pow hq]

theorem hasSubst_xpow {q : ℕ} (hq : q ≠ 0) : HasSubst (xpow σ A q) :=
  hasSubst_of_constantCoeff_zero (constantCoeff_xpow hq)

theorem prod_xpow_pow (q : ℕ) (d : σ →₀ ℕ) :
    (d.prod fun s n => xpow σ A q s ^ n) = MvPowerSeries.monomial (q • d) (1 : A) := by
  rw [Finsupp.prod_fintype _ _ (fun i => pow_zero _)]
  have h : ∀ i : σ, xpow σ A q i ^ d i = MvPowerSeries.monomial (Finsupp.single i ((q • d) i)) (1 : A) := by
    intro i
    rw [xpow, ← pow_mul, MvPowerSeries.X_pow_eq, Finsupp.smul_apply, smul_eq_mul]
  simp_rw [h]
  rw [MvPowerSeries.prod_monomial, Finset.prod_const_one, Finsupp.univ_sum_single]

theorem le_smul_self {q : ℕ} (hq : q ≠ 0) (d : σ →₀ ℕ) : d ≤ q • d := by
  intro i
  rw [Finsupp.smul_apply, smul_eq_mul]
  exact Nat.le_mul_of_pos_left _ (Nat.pos_of_ne_zero hq)

theorem coeff_subst_xpow {q : ℕ} (hq : q ≠ 0) (g : MvPowerSeries σ A) (n : σ →₀ ℕ) :
    coeff n (subst (xpow σ A q) g) = ∑ d ∈ Finset.Iic n, if n = q • d then coeff d g else 0 := by
  classical
  rw [MvPowerSeries.coeff_subst (hasSubst_xpow hq)]
  have h : ∀ d : σ →₀ ℕ,
      coeff d g • coeff n (d.prod fun s m => xpow σ A q s ^ m) = if n = q • d then coeff d g else 0 := by
    intro d
    rw [prod_xpow_pow, MvPowerSeries.coeff_monomial]
    by_cases hd : n = q • d
    · rw [if_pos hd, if_pos hd, smul_eq_mul, mul_one]
    · rw [if_neg hd, if_neg hd, smul_zero]
  simp_rw [h]
  apply finsum_eq_sum_of_support_subset
  intro d hd
  rw [Function.mem_support] at hd
  have hnd : n = q • d := by by_contra h'; exact hd (if_neg h')
  rw [Finset.mem_coe, Finset.mem_Iic, hnd]
  exact le_smul_self hq d

variable {p : ℕ} (hp : p.Prime) (hpA : (p : A) = 0)

include hp hpA in

theorem add_pow_ppow (x y : MvPowerSeries σ A) (j : ℕ) : (x + y) ^ p ^ j = x ^ p ^ j + y ^ p ^ j := by
  have hpS : (p : MvPowerSeries σ A) = 0 := by
    rw [← map_natCast (MvPowerSeries.C (σ := σ) (R := A)) p, hpA, map_zero]
  rw [add_pow_prime_pow_eq hp x y j, hpS]
  ring

include hp hpA in
theorem sum_pow_ppow {ι : Type*} (s : Finset ι) (x : ι → MvPowerSeries σ A) (j : ℕ) :
    (∑ i ∈ s, x i) ^ p ^ j = ∑ i ∈ s, x i ^ p ^ j := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty, Finset.sum_empty, zero_pow (pow_ne_zero _ hp.ne_zero)]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, add_pow_ppow hp hpA, ih]

include hp hpA in

theorem coeff_pow_ppow (f : MvPowerSeries σ A) (j : ℕ) (n : σ →₀ ℕ) :
    coeff n (f ^ p ^ j) = ∑ d ∈ Finset.Iic n, if n = p ^ j • d then coeff d f ^ p ^ j else 0 := by
  classical
  set q : ℕ := p ^ j with hq
  have hq0 : q ≠ 0 := pow_ne_zero _ hp.ne_zero

  set P : MvPowerSeries σ A := ∑ d ∈ Finset.Iic n, MvPowerSeries.monomial d (coeff d f) with hP
  set g : MvPowerSeries σ A := f - P with hg
  have hgcoeff : ∀ a, a ≤ n → coeff a g = 0 := by
    intro a ha
    rw [hg, map_sub, hP, map_sum]
    simp_rw [MvPowerSeries.coeff_monomial]
    rw [Finset.sum_ite_eq, if_pos (Finset.mem_Iic.2 ha), sub_self]
  have hf : f = P + g := by rw [hg]; abel

  have hgq : coeff n (g ^ q) = 0 := by
    obtain ⟨q', hq'⟩ := Nat.exists_eq_succ_of_ne_zero hq0
    rw [hq', pow_succ', MvPowerSeries.coeff_mul]
    apply Finset.sum_eq_zero
    intro x hx
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
    rw [hgcoeff x.1 (by rw [← hx]; exact le_self_add), zero_mul]

  have hPq : P ^ q = ∑ d ∈ Finset.Iic n, MvPowerSeries.monomial (q • d) (coeff d f ^ q) := by
    rw [hP, hq, sum_pow_ppow hp hpA]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [MvPowerSeries.monomial_pow]
  conv_lhs => rw [hf, add_pow_ppow hp hpA, ← hq, map_add, hgq, add_zero, hPq, map_sum]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [MvPowerSeries.coeff_monomial]

include hp hpA in

theorem subst_xpow_map_eq_pow (τ : A →+* A) (j : ℕ) (hτ : ∀ a, τ a = a ^ p ^ j) (f : MvPowerSeries σ A) :
    subst (xpow σ A (p ^ j)) (MvPowerSeries.map τ f) = f ^ p ^ j := by
  classical
  ext n
  rw [coeff_subst_xpow (pow_ne_zero _ hp.ne_zero), coeff_pow_ppow hp hpA]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [MvPowerSeries.coeff_map, hτ]

theorem subst_X_pow {τ' : Type*} (a : σ → MvPowerSeries τ' A) (ha : HasSubst a) (s : σ) (m : ℕ) :
    subst a ((MvPowerSeries.X s : MvPowerSeries σ A) ^ m) = a s ^ m := by
  rw [MvPowerSeries.subst_pow ha, subst_X ha]

end Key

section FrobHom

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal

variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A]

theorem frobSeries_eq_xpow (j : ℕ) : Rigidified.frobSeries (p := p) A j = xpow (Fin 2) A (p ^ j) := rfl

theorem isODHom_frobSeries (hpA : (p : A) = 0) (τ : A →+* A) (j : ℕ) (hτ : ∀ a, τ a = a ^ p ^ j)
    (Y : FormalODModule p A) :
    FormalODModule.IsODHom Y (Y.map τ) (Rigidified.frobSeries (p := p) A j) := by
  classical
  have hp : p.Prime := Fact.out
  have hq0 : p ^ j ≠ 0 := pow_ne_zero _ hp.ne_zero
  have key2 : ∀ f : MvPowerSeries (Fin 2) A,
      subst (Rigidified.frobSeries (p := p) A j) (MvPowerSeries.map τ f) = f ^ p ^ j :=
    fun f => subst_xpow_map_eq_pow hp hpA τ j hτ f

  have compR : ∀ (φ : Series A), (∀ i, constantCoeff (φ i) = 0) →
      (Rigidified.frobSeries (p := p) A j).comp φ = fun i => φ i ^ p ^ j := by
    intro φ hφ
    funext i
    exact subst_X_pow φ (hasSubst_of_constantCoeff_zero hφ) i _

  have compL : ∀ (φ : Series A), (φ.map τ).comp (Rigidified.frobSeries (p := p) A j) = fun i => φ i ^ p ^ j := by
    intro φ
    funext i
    exact key2 (φ i)
  refine ⟨⟨fun i => constantCoeff_xpow hq0 i, fun i => ?_⟩, fun a => ?_, ?_⟩
  ·
    have hL : subst Y.F.toPowerSeries (Rigidified.frobSeries (p := p) A j i) = Y.F.toPowerSeries i ^ p ^ j :=
      subst_X_pow _ Y.F.hasSubst_toPowerSeries i _
    rw [hL]

    have hXl : HasSubst (fun l : Fin 2 => (MvPowerSeries.X (Sum.inl l) : MvPowerSeries (Fin 2 ⊕ Fin 2) A)) :=
      hasSubst_of_constantCoeff_zero (fun l => MvPowerSeries.constantCoeff_X _)
    have hXr : HasSubst (fun l : Fin 2 => (MvPowerSeries.X (Sum.inr l) : MvPowerSeries (Fin 2 ⊕ Fin 2) A)) :=
      hasSubst_of_constantCoeff_zero (fun l => MvPowerSeries.constantCoeff_X _)
    have hfam : (Sum.elim
        (fun l => subst (fun l' => (MvPowerSeries.X (Sum.inl l') : MvPowerSeries (Fin 2 ⊕ Fin 2) A))
          (Rigidified.frobSeries (p := p) A j l))
        (fun l => subst (fun l' => (MvPowerSeries.X (Sum.inr l') : MvPowerSeries (Fin 2 ⊕ Fin 2) A))
          (Rigidified.frobSeries (p := p) A j l))) = xpow (Fin 2 ⊕ Fin 2) A (p ^ j) := by
      funext s
      rcases s with l | l
      · simp only [Sum.elim_inl]
        exact subst_X_pow _ hXl l _
      · simp only [Sum.elim_inr]
        exact subst_X_pow _ hXr l _
    rw [hfam]
    show _ = subst (xpow (Fin 2 ⊕ Fin 2) A (p ^ j)) (MvPowerSeries.map τ (Y.F.toPowerSeries i))
    exact (subst_xpow_map_eq_pow hp hpA τ j hτ _).symm
  ·
    rw [compR _ (Y.isLawHom_act a).1, FormalODModule.map_act, compL]
  ·
    rw [compR _ Y.isLawHom_varpi.1, FormalODModule.map_varpi, compL]

end FrobHom

section Frame

variable {r : ℕ} [Fact r.Prime] {k : Type} [Field k] [CharP k r] [IsAlgClosed k]
variable [Algebra ℤ_[r] (WittVector r k)]

local notation "Frob" => (WittVector.frobenius : WittVector r k →+* WittVector r k)

abbrev frPow (Fr : (WittVector r k) ≃ₐ[ℤ_[r]] (WittVector r k)) (n : ℤ) : (WittVector r k) →+* (WittVector r k) :=
  (((Fr ^ n : (WittVector r k) ≃ₐ[ℤ_[r]] (WittVector r k)) : (WittVector r k) →ₐ[ℤ_[r]] (WittVector r k)) : (WittVector r k) →+* (WittVector r k))

theorem frPow_natCast (Fr : (WittVector r k) ≃ₐ[ℤ_[r]] (WittVector r k)) (hFr : ∀ x : (WittVector r k), Fr x = WittVector.frobenius x) (n : ℕ) :
    frPow Fr (n : ℤ) = Frob ^ n := by
  rw [frPow, zpow_natCast]
  refine RingHom.ext fun x => ?_
  show (Fr ^ n) x = (WittVector.frobenius ^ n) x
  induction n generalizing x with
  | zero => simp
  | succ n ih => rw [pow_succ, pow_succ, AlgEquiv.mul_apply, RingHom.coe_mul, Function.comp_apply, hFr, ih]

theorem comp_frPow_comp_pow (Fr : (WittVector r k) ≃ₐ[ℤ_[r]] (WittVector r k)) (hFr : ∀ x : (WittVector r k), Fr x = WittVector.frobenius x)
    {L : Type} [CommRing L] (ψ : (WittVector r k) →+* L) (z : ℤ) (j : ℕ) :
    (ψ.comp (frPow Fr z)).comp (Frob ^ j) = ψ.comp (frPow Fr (z + j)) := by
  rw [RingHom.comp_assoc]
  congr 1
  rw [← frPow_natCast Fr hFr j]
  refine RingHom.ext fun x => ?_
  show (Fr ^ z) ((Fr ^ (j : ℤ)) x) = (Fr ^ (z + j)) x
  rw [zpow_add, AlgEquiv.mul_apply]

theorem comp_pow_add {L : Type} [CommRing L] (χ : (WittVector r k) →+* L) (a b : ℕ) :
    χ.comp (Frob ^ (a + b)) = (χ.comp (Frob ^ a)).comp (Frob ^ b) := by
  rw [pow_add, RingHom.comp_assoc]; rfl

theorem comp_pow_zero {L : Type} [CommRing L] (χ : (WittVector r k) →+* L) : χ.comp (Frob ^ 0) = χ := by
  rw [pow_zero]; rfl

end Frame

section Witt

variable {r : ℕ} [Fact r.Prime] {k : Type} [Field k] [CharP k r] [IsAlgClosed k]

local notation "Frob" => (WittVector.frobenius : WittVector r k →+* WittVector r k)

theorem sub_coeff_zero (x y : WittVector r k) : (x - y).coeff 0 = x.coeff 0 - y.coeff 0 := by
  have h := WittVector.add_coeff_zero (x - y) y
  rw [sub_add_cancel] at h
  rw [h, add_sub_cancel_right]

theorem pow_coeff_zero (x : WittVector r k) (n : ℕ) : (x ^ n).coeff 0 = x.coeff 0 ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, WittVector.one_coeff_zero]
  | succ n ih => rw [pow_succ, pow_succ, WittVector.mul_coeff_zero, ih]

theorem exists_eq_p_mul_of_coeff_zero (y : WittVector r k) (hy : y.coeff 0 = 0) :
    ∃ z : WittVector r k, y = (r : WittVector r k) * z := by
  have hV : y = WittVector.verschiebung (y.shift 1) := by
    have := WittVector.eq_iterate_verschiebung (x := y) (n := 1) (fun i hi => by
      have : i = 0 := by omega
      subst this; exact hy)
    simpa using this
  obtain ⟨z, hz⟩ := (WittVector.frobenius_bijective r k).2 (y.shift 1)
  refine ⟨z, ?_⟩
  rw [hV, ← hz, WittVector.verschiebung_frobenius, mul_comm]

theorem mk_frobenius (w : WittVector r k) :
    Ideal.Quotient.mk (pIdeal r (WittVector r k)) (WittVector.frobenius w) =
      Ideal.Quotient.mk (pIdeal r (WittVector r k)) w ^ r := by
  rw [← map_pow, Ideal.Quotient.eq]
  obtain ⟨z, hz⟩ := exists_eq_p_mul_of_coeff_zero (WittVector.frobenius w - w ^ r)
    (by rw [sub_coeff_zero, WittVector.coeff_frobenius_charP, pow_coeff_zero, sub_self])
  rw [hz]
  exact Ideal.mul_mem_right _ _ (Ideal.subset_span rfl)

theorem mk_frobenius_pow (j : ℕ) (w : WittVector r k) :
    Ideal.Quotient.mk (pIdeal r (WittVector r k)) ((Frob ^ j) w) =
      Ideal.Quotient.mk (pIdeal r (WittVector r k)) w ^ r ^ j := by
  induction j generalizing w with
  | zero => simp
  | succ j ih => rw [pow_succ', RingHom.coe_mul, Function.comp_apply, mk_frobenius, ih, ← pow_mul, ← pow_succ]

theorem residueMap_comp_frobenius_pow {L : Type} [CommRing L] (χ : WittVector r k →+* L) (j : ℕ)
    (τ : L ⧸ pIdeal r L →+* L ⧸ pIdeal r L) (hτ : ∀ a, τ a = a ^ r ^ j) :
    residueMap (p := r) (χ.comp (Frob ^ j)) = τ.comp (residueMap (p := r) χ) := by
  apply Ideal.Quotient.ringHom_ext
  refine RingHom.ext fun w => ?_
  simp only [RingHom.comp_apply]
  rw [residueMap, Ideal.quotientMap_mk, hτ, residueMap, ← map_pow, ← mk_frobenius_pow, Ideal.quotientMap_mk]
  rfl

theorem frobenius_frobenius_zp2 (a : Zp2 r) : WittVector.frobenius (WittVector.frobenius a) = a := by
  letI : Fintype (GaloisField r 2) := Fintype.ofFinite _
  have hcard : Fintype.card (GaloisField r 2) = r ^ 2 := by
    rw [← Nat.card_eq_fintype_card, GaloisField.card r 2 two_ne_zero]
  ext n
  rw [WittVector.coeff_frobenius_charP, WittVector.coeff_frobenius_charP, ← pow_mul, ← sq, ← hcard,
    FiniteField.pow_card]

theorem frobenius_pow_comp_iota (ι : Zp2 r →+* WittVector r k) (j : ℕ) : (Frob ^ (2 * j)).comp ι = ι := by
  induction j with
  | zero => rw [Nat.mul_zero, pow_zero]; rfl
  | succ j ih =>
      rw [show 2 * (j + 1) = 2 * j + 2 by ring, pow_add]
      refine RingHom.ext fun a => ?_
      show (Frob ^ (2 * j) * Frob ^ 2) (ι a) = ι a
      have h2 : (Frob ^ 2) (ι a) = ι a := by
        rw [sq, RingHom.coe_mul, Function.comp_apply, ← WittVector.ringHom_map_frobenius_of_finite r ι,
          ← WittVector.ringHom_map_frobenius_of_finite r ι, frobenius_frobenius_zp2]
      rw [RingHom.coe_mul, Function.comp_apply, h2]
      exact RingHom.congr_fun ih a

theorem exists_powRingHom (L : Type) [CommRing L] (j : ℕ) :
    ∃ τ : L ⧸ pIdeal r L →+* L ⧸ pIdeal r L, ∀ a, τ a = a ^ r ^ j := by
  have hp : r.Prime := Fact.out
  have hpL : ((r : ℕ) : L ⧸ pIdeal r L) = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk (pIdeal r L)) r, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.subset_span rfl
  rcases subsingleton_or_nontrivial (L ⧸ pIdeal r L) with hL | hL
  · exact ⟨RingHom.id _, fun a => Subsingleton.elim _ _⟩
  · haveI : CharP (L ⧸ pIdeal r L) r := (CharP.charP_iff_prime_eq_zero hp).2 hpL
    haveI : ExpChar (L ⧸ pIdeal r L) r := ExpChar.prime hp
    exact ⟨iterateFrobenius _ r j, fun a => iterateFrobenius_def r j a⟩

end Witt

section Main

variable {r : ℕ} [Fact r.Prime] {k : Type} [Field k] [CharP k r] [IsAlgClosed k]
variable [Algebra ℤ_[r] (WittVector r k)]

local notation "Frob" => (WittVector.frobenius : WittVector r k →+* WittVector r k)

theorem Xbar_congr {Φ : FormalODModule r ((WittVector r k) ⧸ pIdeal r (WittVector r k))}
    {L : Type} [CommRing L] {s s' : Rigidified r Φ L} (h : s'.X = s.X) : s'.Xbar = s.Xbar := by
  show s'.X.map _ = s.X.map _; rw [h]

theorem main
    (Fr : (WittVector r k) ≃ₐ[ℤ_[r]] (WittVector r k)) (hFr : ∀ x : (WittVector r k), Fr x = WittVector.frobenius x)
    (ι : Zp2 r →+* (WittVector r k)) (Φ : FormalODModule r ((WittVector r k) ⧸ pIdeal r (WittVector r k)))
    (hGLdef : ∀ (B : Type) [CommRing B] [IsNoetherianRing B] (ψ : WittVector r k →+* B) (t : Rigidified r Φ B), t.IsAdmissible ι ψ →
      ∀ (e : Subring.centralizer (Set.range Φ.actEnd ∪ {Φ.varpiEnd})) (m' : ℕ),
        FormalODModule.HasKernelOfDegree (e : MvFormalGroup.End Φ.F).toPowerSeries (r ^ (2 * m')) →
        ∃ t' : Rigidified r Φ B,
          t'.IsAdmissible ι (ψ.comp ((WittVector.frobenius : WittVector r k →+* WittVector r k) ^ m')) ∧
          t'.X = t.X ∧
          ∃ c : ℕ,
            (t.Xbar.act ((r : Zp2 r) ^ (c + t.n))).comp
                (t'.ρ.comp fun i => (MvPowerSeries.X i : MvPowerSeries (Fin 2) (B ⧸ pIdeal r B)) ^ (r ^ m')) =
              (t.Xbar.act ((r : Zp2 r) ^ (c + t'.n))).comp
                (t.ρ.comp (Series.map (residueMap ψ) (e : MvFormalGroup.End Φ.F).toPowerSeries)))
    (L : Type) [CommRing L] [IsNoetherianRing L] (ψ : WittVector r k →+* L) (t : Rigidified r Φ L)
    (ht : t.IsAdmissible ι ψ)
    (e : Subring.centralizer (Set.range Φ.actEnd ∪ {Φ.varpiEnd})) (kk m' : ℕ)
    (he : FormalODModule.HasKernelOfDegree (e : MvFormalGroup.End Φ.F).toPowerSeries (r ^ (2 * m'))) :
    ∃ t' : Rigidified r Φ L, t'.IsAdmissible ι (ψ.comp (frPow Fr ((m' : ℤ) - 2 * kk))) ∧
      Rigidified.IsTranslate (e : MvFormalGroup.End Φ.F).toPowerSeries kk m' ψ t t' := by
  have hp : r.Prime := Fact.out
  set ψ' : WittVector r k →+* L := ψ.comp (frPow Fr ((m' : ℤ) - 2 * kk)) with hψ'
  set ℓ₀ : WittVector r k →+* L := ψ.comp (Frob ^ m') with hℓ₀
  set Lb : Type := L ⧸ pIdeal r L
  have hleg : ψ'.comp (Frob ^ (2 * kk)) = ℓ₀ := by
    rw [hψ', comp_frPow_comp_pow Fr hFr, hℓ₀, ← frPow_natCast Fr hFr]
    congr 2; push_cast; ring

  obtain ⟨t₀, ht₀, hX₀, c₀, hc₀⟩ := hGLdef L ψ t ht e m' he
  have hρ0 : ∀ l, constantCoeff (t.ρ l) = 0 := ht.constantCoeff_ρ
  have hρ₀0 : ∀ l, constantCoeff (t₀.ρ l) = 0 := ht₀.constantCoeff_ρ
  set eS : Series Lb := Series.map (residueMap ψ) (e : MvFormalGroup.End Φ.F).toPowerSeries with heS
  have heS0 : ∀ l, constantCoeff (eS l) = 0 := fun l => by
    rw [heS, Series.map, MvPowerSeries.constantCoeff_map, (e : MvFormalGroup.End Φ.F).constantCoeff_eq_zero l, map_zero]
  have hF : ∀ (j : ℕ) l, constantCoeff (Rigidified.frobSeries (p := r) Lb j l) = 0 :=
    fun j => constantCoeff_frobSeries j

  let t' : Rigidified r Φ L := ⟨t.X, t₀.n + kk, t₀.ρ.comp (Rigidified.frobSeries (p := r) Lb (2 * kk))⟩
  have hXbar' : t'.Xbar = t.Xbar := rfl
  have hXbar₀ : t₀.Xbar = t.Xbar := Xbar_congr hX₀
  refine ⟨t', ⟨?_, ht.2.1, ?_, ?_⟩, rfl, c₀, ?_⟩
  ·
    have hstr : structureMap ι ψ' = structureMap ι ℓ₀ := by
      show ψ'.comp ι = ℓ₀.comp ι
      rw [← hleg, RingHom.comp_assoc ι _ ψ', frobenius_pow_comp_iota]
    show t.X.IsSpecial (structureMap ι ψ')
    rw [hstr, ← hX₀]
    exact ht₀.1
  ·
    obtain ⟨τ, hτ⟩ := exists_powRingHom (r := r) L (2 * kk)
    have hpL : ((r : ℕ) : Lb) = 0 := by
      show ((r : ℕ) : L ⧸ pIdeal r L) = 0
      rw [← map_natCast (Ideal.Quotient.mk (pIdeal r L)) r, Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.subset_span rfl
    have hfrob : FormalODModule.IsODHom (Φ.map (residueMap (p := r) ψ')) (Φ.map (residueMap (p := r) ℓ₀))
        (Rigidified.frobSeries (p := r) Lb (2 * kk)) := by
      have h := isODHom_frobSeries hpL τ (2 * kk) hτ (Φ.map (residueMap (p := r) ψ'))
      rwa [FormalODModule.map_map, ← residueMap_comp_frobenius_pow ψ' (2 * kk) τ hτ, hleg] at h
    have h₀ : FormalODModule.IsODHom (Φ.map (residueMap (p := r) ℓ₀)) t.Xbar t₀.ρ := by
      rw [← hXbar₀]; exact ht₀.2.2.1
    show FormalODModule.IsODHom (Φ.map (residueMap (p := r) ψ')) t'.Xbar (t₀.ρ.comp (Rigidified.frobSeries (p := r) Lb (2 * kk)))
    rw [hXbar']
    exact h₀.comp hfrob
  ·
    show FormalODModule.HasKernelOfDegree (t₀.ρ.comp (Rigidified.frobSeries (p := r) Lb (2 * kk))) (r ^ (4 * (t₀.n + kk)))
    have h := CerednikDrinfeld.FormalODModule.HasKernelOfDegree.comp_X_pow ht₀.2.2.2 (q := r ^ (2 * kk))
      (pow_ne_zero _ hp.ne_zero)
    have hexp : r ^ (4 * t₀.n) * (r ^ (2 * kk)) ^ 2 = r ^ (4 * (t₀.n + kk)) := by
      rw [← pow_mul, ← pow_add]; congr 1; ring
    rw [hexp] at h
    exact h
  ·
    show (t.Xbar.act ((r : Zp2 r) ^ (c₀ + t.n + kk))).comp
        ((t₀.ρ.comp (Rigidified.frobSeries (p := r) Lb (2 * kk))).comp (Rigidified.frobSeries (p := r) Lb m')) =
      (t.Xbar.act ((r : Zp2 r) ^ (c₀ + (t₀.n + kk)))).comp
        (t.ρ.comp (eS.comp (Rigidified.frobSeries (p := r) Lb (2 * kk))))
    have R3 : sm t.Xbar (c₀ + t.n) (t₀.ρ.comp (Rigidified.frobSeries (p := r) Lb m')) =
        sm t.Xbar (c₀ + t₀.n) (t.ρ.comp eS) := hc₀
    change sm t.Xbar (c₀ + t.n + kk)
        ((t₀.ρ.comp (Rigidified.frobSeries (p := r) Lb (2 * kk))).comp (Rigidified.frobSeries (p := r) Lb m')) =
      sm t.Xbar (c₀ + (t₀.n + kk)) (t.ρ.comp (eS.comp (Rigidified.frobSeries (p := r) Lb (2 * kk))))
    calc sm t.Xbar (c₀ + t.n + kk)
          ((t₀.ρ.comp (Rigidified.frobSeries (p := r) Lb (2 * kk))).comp (Rigidified.frobSeries (p := r) Lb m'))
        = sm t.Xbar kk ((sm t.Xbar (c₀ + t.n) (t₀.ρ.comp (Rigidified.frobSeries (p := r) Lb m'))).comp
            (Rigidified.frobSeries (p := r) Lb (2 * kk))) := by
          rw [Series.comp_assoc _ _ _ (hF _) (hF _), frobSeries_comp_frobSeries, add_comm (2 * kk) m',
            ← frobSeries_comp_frobSeries, ← Series.comp_assoc _ _ _ (hF _) (hF _),
            sm_comp _ _ _ _ (Series.constantCoeff_comp hρ₀0 (hF _)) (hF _), sm_sm _ _ _ _
              (Series.constantCoeff_comp (Series.constantCoeff_comp hρ₀0 (hF _)) (hF _)), add_comm kk]
      _ = sm t.Xbar kk ((sm t.Xbar (c₀ + t₀.n) (t.ρ.comp eS)).comp (Rigidified.frobSeries (p := r) Lb (2 * kk))) := by
          rw [R3]
      _ = sm t.Xbar (c₀ + (t₀.n + kk)) (t.ρ.comp (eS.comp (Rigidified.frobSeries (p := r) Lb (2 * kk)))) := by
          rw [sm_comp _ _ _ _ (Series.constantCoeff_comp hρ0 heS0) (hF _), Series.comp_assoc _ _ _ heS0 (hF _),
            sm_sm _ _ _ _ (Series.constantCoeff_comp hρ0 (Series.constantCoeff_comp heS0 (hF _)))]
          congr 1; ring

end Main

end R4TranslateExists

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal in

theorem solution
    {r : ℕ} [Fact r.Prime] (k : Type) [Field k] [CharP k r] [IsAlgClosed k]
    [Algebra ℤ_[r] (WittVector r k)]
    (Fr : WittVector r k ≃ₐ[ℤ_[r]] WittVector r k) (hFr : ∀ x : WittVector r k, Fr x = WittVector.frobenius x)
    (ι : Zp2 r →+* WittVector r k)
    (Φ : FormalODModule r (WittVector r k ⧸ pIdeal r (WittVector r k)))

    (hGLdef : ∀ (B : Type) [CommRing B] [IsNoetherianRing B] (ψ : WittVector r k →+* B) (t : Rigidified r Φ B), t.IsAdmissible ι ψ →
      ∀ (e : Subring.centralizer (Set.range Φ.actEnd ∪ {Φ.varpiEnd})) (m' : ℕ),
        FormalODModule.HasKernelOfDegree (e : MvFormalGroup.End Φ.F).toPowerSeries (r ^ (2 * m')) →
        ∃ t' : Rigidified r Φ B,
          t'.IsAdmissible ι (ψ.comp ((WittVector.frobenius : WittVector r k →+* WittVector r k) ^ m')) ∧
          t'.X = t.X ∧
          ∃ c : ℕ,
            (t.Xbar.act ((r : Zp2 r) ^ (c + t.n))).comp
                (t'.ρ.comp fun i => (MvPowerSeries.X i : MvPowerSeries (Fin 2) (B ⧸ pIdeal r B)) ^ (r ^ m')) =
              (t.Xbar.act ((r : Zp2 r) ^ (c + t'.n))).comp
                (t.ρ.comp (Series.map (residueMap ψ) (e : MvFormalGroup.End Φ.F).toPowerSeries)))
    (L : Type) [CommRing L] [IsNoetherianRing L] (ψ : WittVector r k →+* L) (t : Rigidified r Φ L)
    (ht : t.IsAdmissible ι ψ)
    (e : Subring.centralizer (Set.range Φ.actEnd ∪ {Φ.varpiEnd})) (kk m' : ℕ)
    (he : FormalODModule.HasKernelOfDegree (e : MvFormalGroup.End Φ.F).toPowerSeries (r ^ (2 * m'))) :
    ∃ t' : Rigidified r Φ L,
      t'.IsAdmissible ι
        (ψ.comp (((Fr ^ ((m' : ℤ) - 2 * kk) : WittVector r k ≃ₐ[ℤ_[r]] WittVector r k) :
          WittVector r k →ₐ[ℤ_[r]] WittVector r k) : WittVector r k →+* WittVector r k)) ∧
      Rigidified.IsTranslate (e : MvFormalGroup.End Φ.F).toPowerSeries kk m' ψ t t' :=
  R4TranslateExists.main Fr hFr ι Φ hGLdef L ψ t ht e kk m' he

end

end S_CerednikDrinfeld_SpecialFormal_Rigidified_exists_isAdmissible_and_isTranslate_of_isTranslate_zero
end P2MW
export P2MW.S_CerednikDrinfeld_SpecialFormal_Rigidified_exists_isAdmissible_and_isTranslate_of_isTranslate_zero (solution)
