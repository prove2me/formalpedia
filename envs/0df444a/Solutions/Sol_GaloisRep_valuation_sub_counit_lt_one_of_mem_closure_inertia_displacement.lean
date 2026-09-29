-- Prove2me | solution 1 for GaloisRep.valuation_sub_counit_lt_one_of_mem_closure_inertia_displacement
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/c02a65f9-cb54-5999-a0d0-78d791a42e23

import Definitions.Def_GaloisRep_Flat
import Mathlib.RingTheory.Valuation.Integral
import Theorems.Thm_ValuationSubring_valuation_sub_lt_one_of_mem_inertiaSubgroupIn
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GaloisRep_valuation_sub_counit_lt_one_of_mem_closure_inertia_displacement

set_option autoImplicit false
open Coalgebra

namespace EASY

variable {p : ℕ} [Fact p.Prime] {H : Type} [CommRing H]
  [HopfAlgebra (GaloisRep.ratLocalizedAt p) H] [Module.Finite (GaloisRep.ratLocalizedAt p) H]

local notation "K" => AlgebraicClosure ℚ
local notation "Rp" => GaloisRep.ratLocalizedAt p
local notation "Pt" => WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ)

abbrev Conn (A : ValuationSubring K) (f : Pt) : Prop :=
  ∀ h : H, A.valuation (f h - algebraMap Rp K (counit h)) < 1

theorem mul_lt_one_aux {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀] {a b : Γ₀}
    (ha : a < 1) (hb : b ≤ 1) : a * b < 1 :=
  lt_of_le_of_lt (mul_le_mul_right hb a) (by rwa [mul_one])

theorem mul_lt_one_aux' {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀] {a b : Γ₀}
    (ha : a ≤ 1) (hb : b < 1) : a * b < 1 := by
  rw [mul_comm]; exact mul_lt_one_aux hb ha

theorem algebraMap_mem (A : ValuationSubring K) (hA : A.LiesOverPrime p) (r : Rp) :
    algebraMap Rp K r ∈ A := by
  have hcop : (r : ℚ).den.Coprime p := r.2
  have e1 : algebraMap Rp K r = ((r : ℚ) : K) := rfl
  rw [e1, Rat.cast_def, div_eq_mul_inv]
  refine A.mul_mem _ _ (intCast_mem A _) ?_

  have hv1 : A.valuation (((r : ℚ).den : K)) = 1 := by
    refine le_antisymm ((A.valuation_le_one_iff _).mpr (natCast_mem A _)) ?_
    by_contra hlt
    push Not at hlt
    have hp : A.valuation (p : K) < 1 := A.mem_nonunits_iff.mp hA
    have hcop' : IsCoprime (((r : ℚ).den : ℤ)) (p : ℤ) := Nat.isCoprime_iff_coprime.mpr hcop
    obtain ⟨a, b, hab⟩ := hcop'
    have e2 : (a : K) * (((r : ℚ).den : ℕ) : K) + (b : K) * (p : K) = 1 := by exact_mod_cast hab
    have : A.valuation (1 : K) < 1 := by
      rw [← e2]
      exact A.valuation.map_add_lt
        (by rw [map_mul]; exact mul_lt_one_aux' ((A.valuation_le_one_iff _).mpr (intCast_mem A a)) hlt)
        (by rw [map_mul]; exact mul_lt_one_aux' ((A.valuation_le_one_iff _).mpr (intCast_mem A b)) hp)
    rw [map_one] at this
    exact lt_irrefl _ this
  rw [← A.valuation_le_one_iff, map_inv₀, hv1, inv_one]

theorem apply_mem (A : ValuationSubring K) (hA : A.LiesOverPrime p) (f : Pt) (h : H) :
    (f h : K) ∈ A := by
  have hint : IsIntegral Rp h := Algebra.IsIntegral.isIntegral h
  have hint2 : IsIntegral Rp ((WithConv.ofConv f : H →ₐ[Rp] K) h) := hint.map _
  obtain ⟨P, hPmonic, hPeval⟩ := hint2
  let φ : Rp →+* ↥A := (algebraMap Rp K).codRestrict A.toSubring (fun r => algebraMap_mem A hA r)
  have hφ : (algebraMap ↥A K).comp φ = algebraMap Rp K := RingHom.ext fun r => rfl
  have hint3 : IsIntegral ↥A (f h : K) := by
    refine ⟨P.map φ, hPmonic.map φ, ?_⟩
    rw [Polynomial.eval₂_map, hφ]
    exact hPeval
  have hv : A.valuation.Integers ↥A :=
    { hom_inj := Subtype.val_injective
      map_le_one := fun a => (A.valuation_le_one_iff _).mpr a.2
      exists_of_le_one := fun r hr => ⟨⟨r, (A.valuation_le_one_iff r).mp hr⟩, rfl⟩ }
  exact (A.valuation_le_one_iff _).mp ((hv.isIntegral_iff_v_le_one).mp hint3)

theorem val_apply_le_one (A : ValuationSubring K) (hA : A.LiesOverPrime p) (f : Pt) (h : H) :
    A.valuation (f h) ≤ 1 :=
  (A.valuation_le_one_iff _).mpr (apply_mem A hA f h)

theorem val_algebraMap_le_one (A : ValuationSubring K) (hA : A.LiesOverPrime p) (r : Rp) :
    A.valuation (algebraMap Rp K r) ≤ 1 :=
  (A.valuation_le_one_iff _).mpr (algebraMap_mem A hA r)

theorem conn_one (A : ValuationSubring K) : Conn A (1 : Pt) := by
  intro h
  rw [AlgHom.convOne_apply, sub_self, map_zero]
  exact zero_lt_one

theorem convMul_apply_repr (f g : Pt) {h : H} {ι𝓡 : Type*} (𝓡 : Coalgebra.Repr Rp h ι𝓡) :
    (f * g) h = ∑ i ∈ 𝓡.index, f (𝓡.left i) * g (𝓡.right i) := by
  have := congrArg (fun (φ : WithConv (H →ₗ[Rp] K)) => (WithConv.ofConv φ) h)
    (AlgHom.toLinearMap_convMul f g)
  simp only [WithConv.ofConv_toConv, AlgHom.toLinearMap_apply] at this
  rw [this, Coalgebra.Repr.convMul_apply 𝓡]
  rfl

theorem counit_repr {h : H} {ι𝓡 : Type*} (𝓡 : Coalgebra.Repr Rp h ι𝓡) :
    algebraMap Rp K (counit h) =
      ∑ i ∈ 𝓡.index, algebraMap Rp K (counit (𝓡.left i)) *
        algebraMap Rp K (counit (𝓡.right i)) := by
  have h1 := Coalgebra.sum_counit_smul 𝓡
  have h2 : (counit (R := Rp) h) = ∑ i ∈ 𝓡.index, counit (R := Rp) (𝓡.left i) * counit (R := Rp) (𝓡.right i) := by
    conv_lhs => rw [← h1]
    simp [map_sum, map_smul, smul_eq_mul]
  rw [h2, map_sum]
  simp [map_mul]

theorem apply_repr (g : Pt) {h : H} {ι𝓡 : Type*} (𝓡 : Coalgebra.Repr Rp h ι𝓡) :
    (g h : K) = ∑ i ∈ 𝓡.index, algebraMap Rp K (counit (𝓡.left i)) * g (𝓡.right i) := by
  have h1 := Coalgebra.sum_counit_smul 𝓡
  conv_lhs => rw [← h1]
  simp [map_sum, map_smul, Algebra.smul_def]

theorem conn_mul (A : ValuationSubring K) (hA : A.LiesOverPrime p) {f g : Pt}
    (hf : Conn A f) (hg : Conn A g) : Conn A (f * g) := by
  classical
  intro h
  let 𝓡 := Coalgebra.Repr.arbitrary Rp h
  rw [convMul_apply_repr f g 𝓡, counit_repr 𝓡, ← Finset.sum_sub_distrib]
  refine A.valuation.map_sum_lt (by exact one_ne_zero) fun i _ => ?_
  have e1 : f (𝓡.left i) * g (𝓡.right i) -
      algebraMap Rp K (counit (𝓡.left i)) * algebraMap Rp K (counit (𝓡.right i)) =
      (f (𝓡.left i) - algebraMap Rp K (counit (𝓡.left i))) * g (𝓡.right i) +
      algebraMap Rp K (counit (𝓡.left i)) *
        (g (𝓡.right i) - algebraMap Rp K (counit (𝓡.right i))) := by ring
  rw [e1]
  refine A.valuation.map_add_lt ?_ ?_
  · rw [map_mul]
    exact mul_lt_one_aux (hf _) (val_apply_le_one A hA g _)
  · rw [map_mul]
    exact mul_lt_one_aux' (val_algebraMap_le_one A hA _) (hg _)

theorem conn_inv (A : ValuationSubring K) (hA : A.LiesOverPrime p) {f f' : Pt}
    (hf : Conn A f) (hff' : f * f' = 1) : Conn A f' := by
  classical
  intro h
  let 𝓡 := Coalgebra.Repr.arbitrary Rp h
  have h1 : algebraMap Rp K (counit h) = ∑ i ∈ 𝓡.index, f (𝓡.left i) * f' (𝓡.right i) := by
    rw [← convMul_apply_repr f f' 𝓡, hff', AlgHom.convOne_apply]
  rw [apply_repr f' 𝓡, h1, ← Finset.sum_sub_distrib]
  refine A.valuation.map_sum_lt (by exact one_ne_zero) fun i _ => ?_
  rw [← sub_mul, map_mul, ← Valuation.map_neg, neg_sub]
  exact mul_lt_one_aux (hf _) (val_apply_le_one A hA f' _)

noncomputable def translate (σ : K ≃ₐ[ℚ] K) (f : Pt) : Pt :=
  WithConv.toConv
    { toRingHom := (σ : K →+* K).comp (WithConv.ofConv f : H →ₐ[Rp] K).toRingHom
      commutes' := fun r => by
        change σ ((WithConv.ofConv f : H →ₐ[Rp] K) (algebraMap Rp H r)) = algebraMap Rp K r
        rw [AlgHom.commutes]
        change σ (algebraMap ℚ K (r : ℚ)) = algebraMap ℚ K (r : ℚ)
        exact σ.commutes (r : ℚ) }

theorem translate_apply (σ : K ≃ₐ[ℚ] K) (f : Pt) (h : H) : translate σ f h = σ (f h) := rfl

theorem conn_displacement (A : ValuationSubring K) (hA : A.LiesOverPrime p)
    {σ : K ≃ₐ[ℚ] K} (hσ : σ ∈ A.inertiaSubgroupIn ℚ) {f f' : Pt} (hff' : f * f' = 1) :
    Conn A (translate σ f * f') := by
  classical
  intro h
  let 𝓡 := Coalgebra.Repr.arbitrary Rp h
  have h1 : algebraMap Rp K (counit h) = ∑ i ∈ 𝓡.index, f (𝓡.left i) * f' (𝓡.right i) := by
    rw [← convMul_apply_repr f f' 𝓡, hff', AlgHom.convOne_apply]
  rw [convMul_apply_repr _ _ 𝓡, h1, ← Finset.sum_sub_distrib]
  refine A.valuation.map_sum_lt (by exact one_ne_zero) fun i _ => ?_
  rw [translate_apply, ← sub_mul, map_mul]
  exact mul_lt_one_aux
    (A.valuation_sub_lt_one_of_mem_inertiaSubgroupIn hσ (apply_mem A hA f _)).2
    (val_apply_le_one A hA f' _)

end EASY

open EASY in
theorem solution
    (p : ℕ) [Fact p.Prime]
    (H : Type) [CommRing H] [HopfAlgebra (GaloisRep.ratLocalizedAt p) H]
    [Module.Finite (GaloisRep.ratLocalizedAt p) H]
    {J : Type} [AddCommGroup J]
    [DistribMulAction (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) J]
    (M : AddSubgroup J)
    (e : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ) ≃ ↥M)
    (he_add : ∀ f g, e (f * g) = e f + e g)
    (he_act : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
      (f g : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ)),
      (∀ x : H, g x = σ (f x)) → ((e g : ↥M) : J) = σ • ((e f : ↥M) : J))
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (m : ↥M)
    (hm : (m : J) ∈ AddSubgroup.closure
      {x : J | ∃ σ ∈ A.inertiaSubgroupIn ℚ, ∃ y ∈ M, x = σ • y - y}) :
    ∀ h : H, A.valuation ((e.symm m) h -
      algebraMap (GaloisRep.ratLocalizedAt p) (AlgebraicClosure ℚ) (Coalgebra.counit h)) < 1 := by
  classical

  have he1 : e 1 = 0 := by
    have := he_add 1 1; rw [one_mul] at this
    exact left_eq_add.mp this
  have hsymm0 : e.symm 0 = 1 := by rw [← he1, Equiv.symm_apply_apply]

  have hsymm_add : ∀ (x y : ↥M), e.symm (x + y) = e.symm x * e.symm y := by
    intro x y; apply e.injective; rw [he_add]; simp
  have hsymm_mul_inv : ∀ (x : J) (hx : x ∈ M),
      e.symm ⟨x, hx⟩ * e.symm ⟨-x, M.neg_mem hx⟩ = 1 := by
    intro x hx; rw [← hsymm_add, ← hsymm0]; congr 1; ext; simp

  suffices hP : ∃ hx : (m : J) ∈ M, Conn A (e.symm ⟨(m : J), hx⟩) by
    obtain ⟨hx, hc⟩ := hP
    have : (⟨(m : J), hx⟩ : ↥M) = m := Subtype.ext rfl
    rw [this] at hc
    exact hc
  refine AddSubgroup.closure_induction (p := fun x _ => ∃ hx : x ∈ M, Conn A (e.symm ⟨x, hx⟩))
    ?_ ?_ ?_ ?_ hm
  ·
    rintro x ⟨σ, hσ, y, hy, rfl⟩
    let f : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ) := e.symm ⟨y, hy⟩
    have hσy : ((e (translate σ f) : ↥M) : J) = σ • y := by
      have := he_act σ f (translate σ f) (fun x => rfl)
      rw [this]; simp [f]
    have hmem : σ • y - y ∈ M := by
      have : σ • y ∈ M := by rw [← hσy]; exact (e (translate σ f)).2
      exact M.sub_mem this hy
    refine ⟨hmem, ?_⟩
    have hprod : e.symm ⟨σ • y - y, hmem⟩ = translate σ f * e.symm ⟨-y, M.neg_mem hy⟩ := by
      apply e.injective
      rw [Equiv.apply_symm_apply, he_add, Equiv.apply_symm_apply]
      ext
      simp only [AddSubgroup.coe_add, hσy]
      abel
    rw [hprod]
    exact conn_displacement A hA hσ (hsymm_mul_inv y hy)
  ·
    refine ⟨M.zero_mem, ?_⟩
    have : (⟨0, M.zero_mem⟩ : ↥M) = 0 := rfl
    rw [this, hsymm0]
    exact conn_one A
  ·
    rintro x y _ _ ⟨hx, hcx⟩ ⟨hy, hcy⟩
    refine ⟨M.add_mem hx hy, ?_⟩
    have : (⟨x + y, M.add_mem hx hy⟩ : ↥M) = ⟨x, hx⟩ + ⟨y, hy⟩ := rfl
    rw [this, hsymm_add]
    exact conn_mul A hA hcx hcy
  ·
    rintro x _ ⟨hx, hcx⟩
    refine ⟨M.neg_mem hx, ?_⟩
    exact conn_inv A hA hcx (hsymm_mul_inv x hx)

end S_GaloisRep_valuation_sub_counit_lt_one_of_mem_closure_inertia_displacement
end P2MW
export P2MW.S_GaloisRep_valuation_sub_counit_lt_one_of_mem_closure_inertia_displacement (solution)
