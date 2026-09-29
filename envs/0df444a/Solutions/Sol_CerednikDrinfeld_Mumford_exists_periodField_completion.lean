-- Prove2me | solution 1 for CerednikDrinfeld.Mumford.exists_periodField_completion
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/d64df71d-e86a-5dc8-841a-d30aa30400c2

import Definitions.Def_CerednikDrinfeld_MumfordUniformization
import Theorems.Thm_ValuationSubring_valuation_map_eq_of_mem_decompositionSubgroup
import Theorems.Thm_ValuationSubring_exists_valuation_eq_zpow_and_exists_pow_eq_of_forall_inertia_smul_completion_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_Mumford_exists_periodField_completion
p2m_attr_erase "instance" "AlgebraicClosure.Rat.isGalois"

set_option autoImplicit false

p2m_open "CerednikDrinfeld P2MW.S_CerednikDrinfeld_Mumford_exists_periodField_completion.CerednikDrinfeld CerednikDrinfeld.Mumford P2MW.S_CerednikDrinfeld_Mumford_exists_periodField_completion.CerednikDrinfeld.Mumford ModularCurve"

noncomputable section

namespace CerednikDrinfeld
namespace Mumford
namespace PeriodField
p2m_open "CerednikDrinfeld.Mumford CerednikDrinfeld"

variable (A : ValuationSubring (AlgebraicClosure ℚ))

local notation "C" => A.valuation.Completion

scoped instance isometric_fact : Fact (A.DecompositionIsometric ℚ) :=
  ⟨fun σ x => ValuationSubring.valuation_map_eq_of_mem_decompositionSubgroup A σ.2 x⟩

def fixedSubfield : Subfield C where
  carrier := {c | ∀ σ : ↥(A.decompositionSubgroup ℚ), σ ∈ A.inertiaSubgroup ℚ → σ • c = c}
  mul_mem' {a b} ha hb := fun σ hσ => by rw [smul_mul', ha σ hσ, hb σ hσ]
  one_mem' := fun σ _ => smul_one σ
  add_mem' {a b} ha hb := fun σ hσ => by rw [smul_add, ha σ hσ, hb σ hσ]
  zero_mem' := fun σ _ => smul_zero σ
  neg_mem' {a} ha := fun σ hσ => by rw [smul_neg, ha σ hσ]
  inv_mem' a ha := fun σ hσ => by rw [smul_inv'', ha σ hσ]

theorem smul_ratCast (σ : ↥(A.decompositionSubgroup ℚ)) (q : ℚ) : σ • ((q : ℚ) : C) = (q : C) := by
  rw [← MulSemiringAction.toRingHom_apply, map_ratCast]

def K : IntermediateField ℚ C :=
  (fixedSubfield A).toIntermediateField (fun q σ _ => by
    rw [show algebraMap ℚ C q = ((q : ℚ) : C) from rfl]
    exact smul_ratCast A σ q)

variable {A}

theorem mem_K_iff (c : C) :
    c ∈ K A ↔ ∀ σ : ↥(A.decompositionSubgroup ℚ), σ ∈ A.inertiaSubgroup ℚ → σ • c = c := Iff.rfl

theorem smul_coe_K (k : ↥(K A)) (σ : ↥(A.decompositionSubgroup ℚ)) (hσ : σ ∈ A.inertiaSubgroup ℚ) :
    σ • (k : C) = (k : C) := (mem_K_iff (k : C)).1 k.2 σ hσ

theorem exists_algEquiv_eq_smul (A : ValuationSubring (AlgebraicClosure ℚ)) (σ : ↥(A.decompositionSubgroup ℚ)) :
    ∃ s : A.valuation.Completion ≃ₐ[ℚ] A.valuation.Completion, ∀ c, s c = σ • c := by
  let e : A.valuation.Completion ≃+* A.valuation.Completion :=
    MulSemiringAction.toRingEquiv (A.decompositionSubgroup ℚ) A.valuation.Completion σ
  refine ⟨AlgEquiv.ofRingEquiv (f := e) (fun q => ?_), fun c => rfl⟩
  rw [Algebra.algebraMap_eq_smul_one, map_rat_smul, map_one]

theorem mem_K_of_forall {c : C}
    (hc : ∀ σ : ↥(A.decompositionSubgroup ℚ),
      (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) ∈ A.inertiaSubgroupIn ℚ →
      ∀ s : A.valuation.Completion ≃ₐ[ℚ] A.valuation.Completion, (∀ x, s x = σ • x) → s c = c) : c ∈ K A := by
  rw [mem_K_iff]
  intro σ hσ
  obtain ⟨s, hs⟩ := exists_algEquiv_eq_smul A σ
  rw [← hs]
  exact hc σ (Subgroup.mem_map.2 ⟨σ, hσ, rfl⟩) s hs

theorem inertia_K (σ : ↥(A.decompositionSubgroup ℚ))
    (hσ : (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) ∈ A.inertiaSubgroupIn ℚ)
    (s : C ≃ₐ[ℚ] C) (hs : ∀ c, s c = σ • c) (k : ↥(K A)) : s (k : C) = (k : C) := by
  obtain ⟨τ, hτ, hτσ⟩ := Subgroup.mem_map.1 hσ
  have : τ = σ := Subtype.ext (by simpa using hτσ)
  rw [hs]
  exact smul_coe_K k σ (this ▸ hτ)

section Ord

variable {r : ℕ} [Fact r.Prime] (hA : A.LiesOverPrime r)

def ι (A : ValuationSubring (AlgebraicClosure ℚ)) : AlgebraicClosure ℚ →+* A.valuation.Completion :=
  (UniformSpace.Completion.coeRingHom (α := WithVal A.valuation)).comp (WithVal.equiv A.valuation).symm.toRingHom

theorem ι_apply (x : AlgebraicClosure ℚ) : ι A x = ((x : AlgebraicClosure ℚ) : A.valuation.Completion) := rfl

theorem v_natCast (n : ℕ) : Valued.v ((n : ℕ) : C) = A.valuation (n : AlgebraicClosure ℚ) := by
  rw [← map_natCast (ι A) n, ι_apply]
  exact Valued.valuedCompletion_apply _

theorem v_r_ne_zero : Valued.v ((r : ℕ) : C) ≠ 0 := by
  rw [v_natCast, ne_eq, map_eq_zero]
  exact_mod_cast (Fact.out : r.Prime).ne_zero

theorem coe_unit_ne_zero (k : (↥(K A))ˣ) : (((k : ↥(K A)) : C)) ≠ 0 := by
  rw [ne_eq, ZeroMemClass.coe_eq_zero]
  exact k.ne_zero

include hA

theorem v_r_lt_one : Valued.v ((r : ℕ) : C) < 1 := by
  rw [v_natCast]
  exact (ValuationSubring.mem_nonunits_iff A).1 hA

theorem exists_ord (k : (↥(K A))ˣ) : ∃ n : ℤ, Valued.v (((k : ↥(K A)) : C)) = Valued.v ((r : ℕ) : C) ^ n :=
  (ValuationSubring.exists_valuation_eq_zpow_and_exists_pow_eq_of_forall_inertia_smul_completion_eq r Fact.out A
    hA).1 _ (coe_unit_ne_zero k) (fun σ hσ => smul_coe_K (k : ↥(K A)) σ hσ)

def ordFun (k : (↥(K A))ˣ) : ℤ := Classical.choose (exists_ord hA k)

theorem ordFun_spec (k : (↥(K A))ˣ) :
    Valued.v (((k : ↥(K A)) : C)) = Valued.v ((r : ℕ) : C) ^ ordFun hA k :=
  Classical.choose_spec (exists_ord hA k)

theorem zpow_v_r_injective : Function.Injective (fun n : ℤ => Valued.v ((r : ℕ) : C) ^ n) :=
  zpow_right_injective₀ (zero_lt_iff.2 (v_r_ne_zero (A := A))) (ne_of_lt (v_r_lt_one hA))

theorem ordFun_mul (k k' : (↥(K A))ˣ) : ordFun hA (k * k') = ordFun hA k + ordFun hA k' := by
  apply zpow_v_r_injective hA
  show Valued.v ((r : ℕ) : C) ^ ordFun hA (k * k') = Valued.v ((r : ℕ) : C) ^ (ordFun hA k + ordFun hA k')
  rw [← ordFun_spec hA (k * k'), zpow_add₀ (v_r_ne_zero (A := A)), ← ordFun_spec hA k, ← ordFun_spec hA k',
    ← map_mul, Units.val_mul, MulMemClass.coe_mul]

def ord : Additive (↥(K A))ˣ →+ ℤ where
  toFun k := ordFun hA (Additive.toMul k)
  map_zero' := by
    apply zpow_v_r_injective hA
    show Valued.v ((r : ℕ) : C) ^ ordFun hA (Additive.toMul 0) = Valued.v ((r : ℕ) : C) ^ (0 : ℤ)
    rw [← ordFun_spec hA, toMul_zero, Units.val_one, OneMemClass.coe_one, map_one, zpow_zero]
  map_add' k k' := by
    show ordFun hA (Additive.toMul (k + k')) = ordFun hA (Additive.toMul k) + ordFun hA (Additive.toMul k')
    rw [toMul_add, ordFun_mul]

theorem ord_apply (k : (↥(K A))ˣ) : ord hA (Additive.ofMul k) = ordFun hA k := rfl

theorem ord_spec (k : (↥(K A))ˣ) :
    Valued.v (((k : ↥(K A)) : C)) = Valued.v ((r : ℕ) : C) ^ (ord hA (Additive.ofMul k)) :=
  ordFun_spec hA k

theorem hensel_K (n : ℕ) (hn : 0 < n) (hrn : ¬ r ∣ n) (k : (↥(K A))ˣ) (hk : ord hA (Additive.ofMul k) = 0) :
    ∃ k' : (↥(K A))ˣ, k' ^ n = k := by
  have hv : Valued.v (((k : ↥(K A)) : C)) = 1 := by rw [ord_spec hA k, hk, zpow_zero]
  obtain ⟨ρ, hρfix, hρn⟩ :=
    (ValuationSubring.exists_valuation_eq_zpow_and_exists_pow_eq_of_forall_inertia_smul_completion_eq r Fact.out A
      hA).2 n hrn _ (fun σ hσ => smul_coe_K (k : ↥(K A)) σ hσ) hv
  have hρK : ρ ∈ K A := (mem_K_iff ρ).2 hρfix
  have hρ0 : (⟨ρ, hρK⟩ : ↥(K A)) ≠ 0 := by
    intro h0
    apply coe_unit_ne_zero k
    have : ρ = 0 := by simpa using congrArg (fun x : ↥(K A) => (x : C)) h0
    rw [← hρn, this, zero_pow (Nat.pos_iff_ne_zero.1 hn)]
  refine ⟨Units.mk0 ⟨ρ, hρK⟩ hρ0, ?_⟩
  ext
  show ((((Units.mk0 (⟨ρ, hρK⟩ : ↥(K A)) hρ0) ^ n : (↥(K A))ˣ) : ↥(K A)) : C) = (((k : ↥(K A)) : C))
  rw [Units.val_pow_eq_pow_val, Units.val_mk0, SubmonoidClass.coe_pow]
  exact hρn

end Ord

end CerednikDrinfeld.Mumford.PeriodField
p2m_reactivate "P2MW.S_CerednikDrinfeld_Mumford_exists_periodField_completion.CerednikDrinfeld P2MW.S_CerednikDrinfeld_Mumford_exists_periodField_completion.CerednikDrinfeld.Mumford P2MW.S_CerednikDrinfeld_Mumford_exists_periodField_completion.CerednikDrinfeld.Mumford.PeriodField"
p2m_reactivate "P2MW.S_CerednikDrinfeld_Mumford_exists_periodField_completion.CerednikDrinfeld P2MW.S_CerednikDrinfeld_Mumford_exists_periodField_completion.CerednikDrinfeld.Mumford"
p2m_reactivate "P2MW.S_CerednikDrinfeld_Mumford_exists_periodField_completion.CerednikDrinfeld"

end
p2m_reactivate "P2MW.S_CerednikDrinfeld_Mumford_exists_periodField_completion.CerednikDrinfeld P2MW.S_CerednikDrinfeld_Mumford_exists_periodField_completion.CerednikDrinfeld.Mumford P2MW.S_CerednikDrinfeld_Mumford_exists_periodField_completion.CerednikDrinfeld.Mumford.PeriodField"

open CerednikDrinfeld.Mumford.PeriodField in
theorem solution
    (r : ℕ) [Fact r.Prime] (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime r) :
    ∃ K : IntermediateField ℚ A.valuation.Completion, ∃ ord : Additive (↥K)ˣ →+ ℤ,
      (∀ k : (↥K)ˣ, Valued.v (((k : ↥K) : A.valuation.Completion)) =
        Valued.v ((r : ℕ) : A.valuation.Completion) ^ (ord (Additive.ofMul k))) ∧
      (∀ σ : ↥(A.decompositionSubgroup ℚ),
        (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) ∈ A.inertiaSubgroupIn ℚ →
        ∀ s : A.valuation.Completion ≃ₐ[ℚ] A.valuation.Completion, (∀ c, s c = σ • c) →
          ∀ k : ↥K, s (k : A.valuation.Completion) = (k : A.valuation.Completion)) ∧
      (∀ n : ℕ, 0 < n → ¬ r ∣ n → ∀ k : (↥K)ˣ, ord (Additive.ofMul k) = 0 → ∃ k' : (↥K)ˣ, k' ^ n = k) ∧
      (∀ c : A.valuation.Completion,
        (∀ σ : ↥(A.decompositionSubgroup ℚ),
          (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) ∈ A.inertiaSubgroupIn ℚ →
          ∀ s : A.valuation.Completion ≃ₐ[ℚ] A.valuation.Completion, (∀ x, s x = σ • x) → s c = c) → c ∈ K) :=
  ⟨K A, ord hA, ord_spec hA, fun σ hσ s hs k => inertia_K σ hσ s hs k, hensel_K hA, fun _ hc => mem_K_of_forall hc⟩

end S_CerednikDrinfeld_Mumford_exists_periodField_completion
end P2MW
export P2MW.S_CerednikDrinfeld_Mumford_exists_periodField_completion (solution)
