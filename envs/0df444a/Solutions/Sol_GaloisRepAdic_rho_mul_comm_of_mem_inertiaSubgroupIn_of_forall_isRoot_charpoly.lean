-- Prove2me | solution 1 for GaloisRepAdic.rho_mul_comm_of_mem_inertiaSubgroupIn_of_forall_isRoot_charpoly
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/04426f3e-6e4f-58df-bf51-8f96713907f1

import Mathlib
import Definitions.Def_GaloisRep_Adic
import Theorems.Thm_ValuationSubring_exists_forall_pow_prime_pow_apply_eq_self_of_wild
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GaloisRepAdic_rho_mul_comm_of_mem_inertiaSubgroupIn_of_forall_isRoot_charpoly

set_option autoImplicit false

namespace InertiaEigenOne

open scoped Pointwise
open Polynomial Module

section Valuation

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

theorem residue_eq_iff (A : ValuationSubring L) (a b : A) :
    IsLocalRing.residue A a = IsLocalRing.residue A b ↔ ((a : L) - b) ∈ A.nonunits := by
  rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff,
    ← ValuationSubring.coe_mem_nonunits_iff]
  rfl

theorem smul_eq_and_sub_mem_of_mem_inertiaSubgroupIn (A : ValuationSubring L) {τ : L ≃ₐ[K] L}
    (hτ : τ ∈ A.inertiaSubgroupIn K) : τ • A = A ∧ ∀ a ∈ A, τ a - a ∈ A.nonunits := by
  obtain ⟨d, hd, rfl⟩ := hτ
  refine ⟨MulAction.mem_stabilizer_iff.1 d.2, fun a ha => ?_⟩
  have hker : ∀ x : IsLocalRing.ResidueField A, d • x = x := fun x => by
    have := RingEquiv.congr_fun (MonoidHom.mem_ker.1 hd) x
    simpa using this
  have h1 := hker (IsLocalRing.residue A ⟨a, ha⟩)
  rw [← IsLocalRing.ResidueField.residue_smul, residue_eq_iff] at h1
  simp at h1
  exact h1

theorem apply_mem_of_smul_eq (A : ValuationSubring L) {τ : L ≃ₐ[K] L} (hτ : τ • A = A) {x : L}
    (hx : x ∈ A) : τ x ∈ A := by
  have : τ • x ∈ τ • A := Set.smul_mem_smul_set (a := τ) hx
  rw [hτ] at this
  exact this

theorem inv_smul_eq_of_smul_eq (A : ValuationSubring L) {τ : L ≃ₐ[K] L} (hτ : τ • A = A) :
    τ⁻¹ • A = A := by
  have := congrArg (fun B : ValuationSubring L => τ⁻¹ • B) hτ
  simpa [smul_smul] using this.symm

theorem mem_of_apply_mem_of_smul_eq (A : ValuationSubring L) {τ : L ≃ₐ[K] L} (hτ : τ • A = A)
    {x : L} (hx : τ x ∈ A) : x ∈ A := by
  have := apply_mem_of_smul_eq A (inv_smul_eq_of_smul_eq A hτ) hx
  simpa [AlgEquiv.aut_inv] using this

theorem valuation_apply_lt_one (A : ValuationSubring L) {τ : L ≃ₐ[K] L} (hτ : τ • A = A)
    {x : L} (hx : A.valuation x < 1) : A.valuation (τ x) < 1 := by
  by_cases hx0 : x = 0
  · simp [hx0]
  by_contra h
  rw [not_lt] at h
  have hxA : x ∈ A := (A.valuation_le_one_iff _).mp hx.le
  have hτxA : τ x ∈ A := apply_mem_of_smul_eq A hτ hxA
  have h1 : A.valuation (τ x) = 1 := le_antisymm ((A.valuation_le_one_iff _).mpr hτxA) h
  have hinv : x⁻¹ ∈ A := by
    refine mem_of_apply_mem_of_smul_eq A hτ ?_
    rw [map_inv₀, ← A.valuation_le_one_iff, map_inv₀, h1, inv_one]
  have h2 : A.valuation x⁻¹ ≤ 1 := (A.valuation_le_one_iff _).mpr hinv
  have hpos : 0 < A.valuation x := zero_lt_iff.mpr (by simpa using hx0)
  rw [map_inv₀, inv_le_one₀ hpos] at h2
  exact absurd hx (not_lt.mpr h2)

theorem valuation_apply_lt_of_lt (A : ValuationSubring L) {τ : L ≃ₐ[K] L} (hτ : τ • A = A)
    {x y : L} (hy : y ≠ 0) (h : A.valuation x < A.valuation y) :
    A.valuation (τ x) < A.valuation (τ y) := by
  have hτy : τ y ≠ 0 := by simpa using hy
  have hvy : 0 < A.valuation y := zero_lt_iff.mpr (by simpa using hy)
  have hvτy : 0 < A.valuation (τ y) := zero_lt_iff.mpr (by simpa using hτy)
  have hxy : A.valuation (x / y) < 1 := by rwa [map_div₀, div_lt_one₀ hvy]
  have := valuation_apply_lt_one A hτ hxy
  rwa [map_div₀, map_div₀, div_lt_one₀ hvτy] at this

theorem valuation_apply_eq [Algebra.IsAlgebraic K L] (A : ValuationSubring L) {τ : L ≃ₐ[K] L}
    (hτ : τ • A = A) (z : L) : A.valuation (τ z) = A.valuation z := by

  have key : ∀ (σ : L ≃ₐ[K] L), σ • A = A → ∀ w : L, ¬ A.valuation (σ w) < A.valuation w := by
    intro σ hσ w hlt
    have hw0 : w ≠ 0 := by
      rintro rfl
      simp at hlt

    have hstep : ∀ n : ℕ, A.valuation ((σ ^ (n + 1)) w) < A.valuation ((σ ^ n) w) := by
      intro n
      induction n with
      | zero => simpa using hlt
      | succ n ih =>
        have hne : (σ ^ n) w ≠ 0 := by
          intro h
          exact hw0 ((σ ^ n).injective (by rw [h, map_zero]))
        have := valuation_apply_lt_of_lt A hσ hne ih
        simpa [pow_succ'] using this
    have hanti : StrictAnti fun n : ℕ => A.valuation ((σ ^ n) w) := strictAnti_nat_of_succ_lt hstep

    have hint : IsIntegral K w := Algebra.IsIntegral.isIntegral w
    have hfin : ((minpoly K w).rootSet L).Finite := Polynomial.rootSet_finite _ _
    have hmem : ∀ n : ℕ, (σ ^ n) w ∈ (minpoly K w).rootSet L := by
      intro n
      rw [Polynomial.mem_rootSet_of_ne (minpoly.ne_zero hint)]
      rw [← AlgEquiv.coe_algHom, Polynomial.aeval_algHom_apply, minpoly.aeval, map_zero]
    obtain ⟨m, n, hmn, hmneq⟩ := hfin.exists_lt_map_eq_of_forall_mem hmem
    exact absurd (congrArg A.valuation hmneq) (hanti hmn).ne'
  rcases lt_trichotomy (A.valuation (τ z)) (A.valuation z) with h | h | h
  · exact absurd h (key τ hτ z)
  · exact h
  · exfalso
    refine key τ⁻¹ (inv_smul_eq_of_smul_eq A hτ) (τ z) ?_
    simpa [AlgEquiv.aut_inv] using h

theorem valuation_apply_div_self [Algebra.IsAlgebraic K L] (A : ValuationSubring L)
    {τ : L ≃ₐ[K] L} (hτ : τ • A = A) {z : L} (hz : z ≠ 0) : A.valuation (τ z / z) = 1 := by
  rw [map_div₀, valuation_apply_eq A hτ z, div_self]
  simpa using hz

theorem valuation_apply_div_self_sub_one_lt (A : ValuationSubring L) {σ : L ≃ₐ[K] L}
    (hσ : σ ∈ A.inertiaSubgroupIn K) {w : L} (hw : A.valuation w = 1) :
    A.valuation (σ w / w - 1) < 1 := by
  have hw0 : w ≠ 0 := by
    rintro rfl
    simp at hw
  have hwA : w ∈ A := (A.valuation_le_one_iff _).mp hw.le
  have h := (smul_eq_and_sub_mem_of_mem_inertiaSubgroupIn A hσ).2 w hwA
  rw [ValuationSubring.mem_nonunits_iff] at h
  have : σ w / w - 1 = (σ w - w) / w := by field_simp
  rw [this, map_div₀, hw, div_one]
  exact h

theorem valuation_cocycle_translate_sub_lt [Algebra.IsAlgebraic K L] (A : ValuationSubring L)
    {σ τ : L ≃ₐ[K] L} (hσ : σ ∈ A.inertiaSubgroupIn K) (hτ : τ • A = A) {z : L} (hz : z ≠ 0) :
    A.valuation (σ (τ z) / τ z - σ z / z) < 1 := by
  set w : L := τ z / z with hw
  have hτz : τ z ≠ 0 := by simpa using hz
  have hwv : A.valuation w = 1 := valuation_apply_div_self A hτ hz
  have hw0 : w ≠ 0 := by
    rintro h0
    rw [h0] at hwv
    simp at hwv
  have hτz' : τ z = w * z := by rw [hw, div_mul_cancel₀ _ hz]
  have hcalc : σ (τ z) / τ z - σ z / z = (σ w / w - 1) * (σ z / z) := by
    rw [hτz', map_mul, mul_div_mul_comm]
    ring
  rw [hcalc, map_mul, valuation_apply_div_self A
    (smul_eq_and_sub_mem_of_mem_inertiaSubgroupIn A hσ).1 hz, mul_one]
  exact valuation_apply_div_self_sub_one_lt A hσ hwv

theorem apply_div_self_mem [Algebra.IsAlgebraic K L] (A : ValuationSubring L) {τ : L ≃ₐ[K] L}
    (hτ : τ • A = A) {z : L} (hz : z ≠ 0) : τ z / z ∈ A :=
  (A.valuation_le_one_iff _).mp (valuation_apply_div_self A hτ hz).le

variable (K) in

noncomputable def tameAt [Algebra.IsAlgebraic K L] (A : ValuationSubring L) (z : L) (hz : z ≠ 0)
    (σ : A.inertiaSubgroupIn K) : IsLocalRing.ResidueField A :=
  IsLocalRing.residue A ⟨σ.1 z / z,
    apply_div_self_mem A (smul_eq_and_sub_mem_of_mem_inertiaSubgroupIn A σ.2).1 hz⟩

theorem tameAt_ne_zero [Algebra.IsAlgebraic K L] (A : ValuationSubring L) (z : L) (hz : z ≠ 0)
    (σ : A.inertiaSubgroupIn K) : tameAt K A z hz σ ≠ 0 := by
  rw [tameAt, Ne, IsLocalRing.residue_eq_zero_iff, ← ValuationSubring.coe_mem_nonunits_iff,
    ValuationSubring.mem_nonunits_iff]
  simp only [not_lt]
  exact (valuation_apply_div_self A (smul_eq_and_sub_mem_of_mem_inertiaSubgroupIn A σ.2).1 hz).ge

theorem tameAt_one [Algebra.IsAlgebraic K L] (A : ValuationSubring L) (z : L) (hz : z ≠ 0) :
    tameAt K A z hz 1 = 1 := by
  rw [tameAt, ← (IsLocalRing.residue A).map_one]
  congr 1
  ext
  simp [div_self hz]

theorem tameAt_mul [Algebra.IsAlgebraic K L] (A : ValuationSubring L) (z : L) (hz : z ≠ 0)
    (σ τ : A.inertiaSubgroupIn K) : tameAt K A z hz (σ * τ) = tameAt K A z hz σ * tameAt K A z hz τ := by
  rw [tameAt, tameAt, tameAt, ← map_mul, residue_eq_iff]
  have hτz : τ.1 z ≠ 0 := by simpa using hz
  have hτA : τ.1 • A = A := (smul_eq_and_sub_mem_of_mem_inertiaSubgroupIn A τ.2).1

  have hsplit : (σ * τ).1 z / z = σ.1 (τ.1 z) / τ.1 z * (τ.1 z / z) := by
    simp only [Subgroup.coe_mul, AlgEquiv.mul_apply]
    field_simp
  simp only [hsplit]
  change σ.1 (τ.1 z) / τ.1 z * (τ.1 z / z) - σ.1 z / z * (τ.1 z / z) ∈ A.nonunits
  rw [ValuationSubring.mem_nonunits_iff, ← sub_mul, map_mul, valuation_apply_div_self A hτA hz,
    mul_one]
  exact valuation_cocycle_translate_sub_lt A σ.2 hτA hz

theorem commutator_apply_mul_inv_sub_one_mem_nonunits [Algebra.IsAlgebraic K L]
    (A : ValuationSubring L) {σ τ : L ≃ₐ[K] L} (hσ : σ ∈ A.inertiaSubgroupIn K)
    (hτ : τ ∈ A.inertiaSubgroupIn K) (z : L) (hz : z ≠ 0) :
    (σ * τ * σ⁻¹ * τ⁻¹) z * z⁻¹ - 1 ∈ A.nonunits := by
  set s : A.inertiaSubgroupIn K := ⟨σ, hσ⟩
  set t : A.inertiaSubgroupIn K := ⟨τ, hτ⟩
  have hθ : tameAt K A z hz (s * t * s⁻¹ * t⁻¹) = 1 := by
    have h1 : tameAt K A z hz (s * t * s⁻¹ * t⁻¹) * tameAt K A z hz (t * s) = tameAt K A z hz (t * s) := by
      rw [← tameAt_mul]
      have : s * t * s⁻¹ * t⁻¹ * (t * s) = s * t := by group
      rw [this, tameAt_mul, tameAt_mul, mul_comm]
    have hne := tameAt_ne_zero A z hz (t * s)
    exact mul_right_cancel₀ hne (by rw [h1, one_mul])
  rw [tameAt, ← (IsLocalRing.residue A).map_one, residue_eq_iff] at hθ
  simpa [div_eq_mul_inv] using hθ

end Valuation

section RankTwo

variable {A : Type*} [CommRing A] [Nontrivial A] {V : Type*} [AddCommGroup V] [Module A V]
  [Module.Free A V] [Module.Finite A V]

theorem det_eq_charpoly_coeff_zero (hV : Module.finrank A V = 2) (f : Module.End A V) :
    LinearMap.det f = f.charpoly.coeff 0 := by
  classical
  let b := Module.Free.chooseBasis A V
  rw [← LinearMap.det_toMatrix b, Matrix.det_eq_sign_charpoly_coeff, LinearMap.charpoly_toMatrix,
    ← Module.finrank_eq_card_basis b, hV]
  ring

theorem charpoly_eq_of_finrank_eq_two (hV : Module.finrank A V = 2) (f : Module.End A V) :
    f.charpoly = X ^ 2 + C (f.charpoly.coeff 1) * X + C (LinearMap.det f) := by
  have hmon := f.charpoly_monic
  have hdeg : f.charpoly.natDegree = 2 := by rw [LinearMap.charpoly_natDegree, hV]
  rw [det_eq_charpoly_coeff_zero hV]
  conv_lhs => rw [hmon.as_sum, hdeg]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, pow_zero, mul_one, pow_one]
  ring

omit [Nontrivial A] in

theorem sub_one_sq_eq_zero_of_charpoly (f : Module.End A V) (h : f.charpoly = (X - 1) ^ 2) :
    (f - 1) ^ 2 = 0 := by
  have hCH := f.aeval_self_charpoly
  rw [h] at hCH
  simpa [map_pow, map_sub, aeval_X] using hCH

theorem charpoly_eq_X_sub_one_sq (hV : Module.finrank A V = 2) (f : Module.End A V)
    (h1 : f.charpoly.IsRoot 1) (hdet : LinearMap.det f = 1) : f.charpoly = (X - 1) ^ 2 := by
  have hform := charpoly_eq_of_finrank_eq_two hV f
  have hroot : f.charpoly.eval 1 = 0 := h1
  rw [hform, hdet] at hroot
  simp only [eval_add, eval_pow, eval_X, one_pow, eval_mul, eval_C, mul_one, map_one,
    eval_one] at hroot

  have hc : f.charpoly.coeff 1 = -2 := by linear_combination hroot
  rw [hform, hdet, hc]
  simp only [map_neg, map_ofNat, map_one]
  ring

end RankTwo

section Adic

p2m_open "IsLocalRing Module.IsLocalRing"
open scoped TensorProduct

theorem normal_algebraicClosure_rat : Normal ℚ (AlgebraicClosure ℚ) := by
  convert @IsAlgClosure.normal ℚ (AlgebraicClosure ℚ) _ _ (AlgebraicClosure.instAlgebra ℚ)
    inferInstance
  rfl

theorem isAlgebraic_algebraicClosure_rat : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) :=
  haveI := normal_algebraicClosure_rat
  inferInstance

theorem exists_normal_ge (L : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ L] :
    ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧ Normal ℚ F ∧ L ≤ F := by
  haveI := normal_algebraicClosure_rat
  exact ⟨IntermediateField.normalClosure ℚ L (AlgebraicClosure ℚ), inferInstance,
    normalClosure.normal ℚ L (AlgebraicClosure ℚ), IntermediateField.le_normalClosure L⟩

theorem one_add_pow_of_mul_self_eq_zero {E : Type*} [Ring E] (N : E) (h : N * N = 0) (m : ℕ) :
    (1 + N) ^ m = 1 + m • N := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ, ih, add_mul, one_mul, mul_add, mul_one, smul_mul_assoc, h, smul_zero, add_zero,
      add_smul, one_smul, add_assoc, add_comm N]

variable {A : Type} [CommRing A] [IsLocalRing A]

theorem apply_eq_one_of_wild_of_sub_one_sq_eq_zero [IsNoetherianRing A] (ρ : GaloisRepAdic A)
    {q : ℕ} (hq : q.Prime) (hqA : IsUnit (q : A))
    (P : ValuationSubring (AlgebraicClosure ℚ)) (hP : P.LiesOverPrime q)
    {κ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ}
    (hwild : ∀ z : AlgebraicClosure ℚ, z ≠ 0 → κ z * z⁻¹ - 1 ∈ P.nonunits)
    (hN : (ρ.ρ κ - 1) ^ 2 = 0) : ρ.ρ κ = 1 := by
  set N : Module.End A ρ.V := ρ.ρ κ - 1 with hNdef
  have hNN : N * N = 0 := by rw [← pow_two]; exact hN
  have hρκ : ρ.ρ κ = 1 + N := by rw [hNdef, add_sub_cancel]
  suffices hN0 : N = 0 by
    rw [hρκ, hN0, add_zero]
  refine LinearMap.ext fun v => ?_
  rw [LinearMap.zero_apply]

  have hmem : N v ∈ (⨅ n : ℕ, (maximalIdeal A ^ n) • (⊤ : Submodule A ρ.V)) := by
    rw [Submodule.mem_iInf]
    intro n
    obtain ⟨L, hL, hcont⟩ := ρ.isAdicContinuous n
    haveI := hL
    obtain ⟨F, hF, hFn, hLF⟩ := exists_normal_ge L
    haveI := hF
    haveI := hFn
    obtain ⟨a, ha⟩ :=
      ValuationSubring.exists_forall_pow_prime_pow_apply_eq_self_of_wild hq P hP hwild F
    have hfix : ∀ x ∈ L, (κ ^ (q ^ a)) x = x := fun x hx => ha x (hLF hx)
    have h1 := hcont (κ ^ (q ^ a)) hfix v
    rw [map_pow, hρκ, one_add_pow_of_mul_self_eq_zero N hNN, LinearMap.add_apply,
      Module.End.one_apply, add_sub_cancel_left, LinearMap.smul_apply] at h1

    have hunit : IsUnit ((q : A) ^ a) := hqA.pow a
    have hcast : (q ^ a) • N v = ((q : A) ^ a) • N v := by
      rw [← Nat.cast_smul_eq_nsmul A, Nat.cast_pow]
    rw [hcast] at h1
    have := Submodule.smul_mem _ (↑hunit.unit⁻¹ : A) h1
    rwa [smul_smul, IsUnit.val_inv_mul, one_smul] at this
  rwa [Ideal.iInf_pow_smul_eq_bot_of_isLocalRing _ (maximalIdeal.isMaximal A).ne_top,
    Submodule.mem_bot] at hmem

theorem inertia_comm [IsDomain A] [IsNoetherianRing A] (ρ : GaloisRepAdic A)
    {q : ℕ} (hq : q.Prime) (hqA : IsUnit (q : A))
    (P : ValuationSubring (AlgebraicClosure ℚ)) (hP : P.LiesOverPrime q)
    (h1 : ∀ σ ∈ P.inertiaSubgroupIn ℚ, (LinearMap.charpoly (ρ.ρ σ)).IsRoot 1)
    {σ τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ}
    (hσ : σ ∈ P.inertiaSubgroupIn ℚ) (hτ : τ ∈ P.inertiaSubgroupIn ℚ) :
    ρ.ρ σ * ρ.ρ τ = ρ.ρ τ * ρ.ρ σ := by
  haveI := isAlgebraic_algebraicClosure_rat
  set κ := σ * τ * σ⁻¹ * τ⁻¹ with hκ
  have hκI : κ ∈ P.inertiaSubgroupIn ℚ :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hσ hτ) (Subgroup.inv_mem _ hσ))
      (Subgroup.inv_mem _ hτ)

  have hdet : LinearMap.det (ρ.ρ κ) = 1 := by
    have hd : ρ.det κ = 1 := by
      simp only [hκ, map_mul, map_inv]
      rw [mul_right_comm (ρ.det σ) (ρ.det τ), mul_inv_cancel, one_mul, mul_inv_cancel]
    have := congrArg (fun u : Aˣ => (u : A)) hd
    simpa [GaloisRepAdic.det] using this

  have hsq : (ρ.ρ κ - 1) ^ 2 = 0 :=
    sub_one_sq_eq_zero_of_charpoly _ (charpoly_eq_X_sub_one_sq ρ.finrank_eq _ (h1 κ hκI) hdet)

  have hwild : ∀ z : AlgebraicClosure ℚ, z ≠ 0 → κ z * z⁻¹ - 1 ∈ P.nonunits :=
    fun z hz => commutator_apply_mul_inv_sub_one_mem_nonunits P hσ hτ z hz
  have hone : ρ.ρ κ = 1 := apply_eq_one_of_wild_of_sub_one_sq_eq_zero ρ hq hqA P hP hwild hsq
  have hgrp : κ * (τ * σ) = σ * τ := by rw [hκ]; group
  have := congrArg ρ.ρ hgrp
  rw [map_mul, hone, one_mul, map_mul, map_mul] at this
  exact this.symm

end Adic

end InertiaEigenOne

open InertiaEigenOne in

theorem solution
    {A : Type} [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A]
    (ρ : GaloisRepAdic A) {q : ℕ} (hq : q.Prime) (hqA : IsUnit (q : A))
    (P : ValuationSubring (AlgebraicClosure ℚ)) (hP : P.LiesOverPrime q)
    (h1 : ∀ σ ∈ P.inertiaSubgroupIn ℚ, (LinearMap.charpoly (ρ.ρ σ)).IsRoot 1)
    {σ τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ}
    (hσ : σ ∈ P.inertiaSubgroupIn ℚ) (hτ : τ ∈ P.inertiaSubgroupIn ℚ) :
    ρ.ρ σ * ρ.ρ τ = ρ.ρ τ * ρ.ρ σ :=
  InertiaEigenOne.inertia_comm ρ hq hqA P hP h1 hσ hτ

end S_GaloisRepAdic_rho_mul_comm_of_mem_inertiaSubgroupIn_of_forall_isRoot_charpoly
end P2MW
export P2MW.S_GaloisRepAdic_rho_mul_comm_of_mem_inertiaSubgroupIn_of_forall_isRoot_charpoly (solution)
