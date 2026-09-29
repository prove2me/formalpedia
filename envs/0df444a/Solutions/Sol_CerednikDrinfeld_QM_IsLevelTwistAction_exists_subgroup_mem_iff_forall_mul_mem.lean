-- Prove2me | solution 1 for CerednikDrinfeld.QM.IsLevelTwistAction.exists_subgroup_mem_iff_forall_mul_mem
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/c672ae80-5dd9-593c-944a-59699fdf1a55

import Definitions.Def_CerednikDrinfeld_QMFineModuli
import Theorems.Thm_QuaternionAlgebra_IsOrder_relIndex_span_smul_eq_pow_four
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_IsLevelTwistAction_exists_subgroup_mem_iff_forall_mul_mem

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra

theorem solution
    {a b : ℚ} (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsOrder Λ) (N m : ℕ) [NeZero m] {B : Type} [CommRing B]
    {M : Scheme.{0}} {πM : M ⟶ Spec (CommRingCat.of B)}
    {ptF : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B)),
      FakeEllipticCurve.WithFullLevel Λ N m S → SchemeHomOver s πM}
    {G : Type} [Group G] {ρ : G →* Aut M} {χ : G → ↥Λ} (hρ : IsLevelTwistAction Λ N m M πM ptF G ρ χ)
    (L₀ : Submodule ℤ ℍ[ℚ, a, b]) (hL₀ : L₀ ≤ Λ) {ℓ : ℕ} (hℓL₀ : ∀ x : ↥Λ, (ℓ : ℚ) • (x : ℍ[ℚ, a, b]) ∈ L₀) (hℓm : ℓ ∣ m)
    (hL₀_left : ∀ (y : ↥Λ) (x : ℍ[ℚ, a, b]), x ∈ L₀ → (y : ℍ[ℚ, a, b]) * x ∈ L₀) :
    ∃ H : Subgroup G, ∀ g : G, g ∈ H ↔ ∀ x : ℍ[ℚ, a, b], x ∈ L₀ → x * (χ g : ℍ[ℚ, a, b]) ∈ L₀ := by
  classical
  have hm0 : 0 < m := Nat.pos_of_ne_zero (NeZero.ne m)

  have habs : ∀ x : ℍ[ℚ, a, b], x ∈ L₀ → ∀ y : ↥Λ, x * ((m : ℚ) • (y : ℍ[ℚ, a, b])) ∈ L₀ := by
    intro x hx y
    obtain ⟨c, hc⟩ := hℓm
    have hxy : x * (y : ℍ[ℚ, a, b]) ∈ Λ := hΛ.mul_mem (hL₀ hx) y.2
    have h1 : (ℓ : ℚ) • (x * (y : ℍ[ℚ, a, b])) ∈ L₀ := hℓL₀ ⟨_, hxy⟩
    have h2 : (c : ℤ) • ((ℓ : ℚ) • (x * (y : ℍ[ℚ, a, b]))) ∈ L₀ := L₀.smul_mem _ h1
    rw [mul_smul_comm, hc, Nat.cast_mul, mul_comm ((ℓ : ℕ) : ℚ), ← smul_smul, Nat.cast_smul_eq_nsmul ℚ c,
      ← natCast_zsmul]
    exact h2

  have hone : ∀ x : ℍ[ℚ, a, b], x ∈ L₀ → x * (χ 1 : ℍ[ℚ, a, b]) ∈ L₀ := by
    intro x hx
    obtain ⟨y, hy⟩ := hρ.label_one
    rw [sub_eq_iff_eq_add] at hy
    rw [hy, mul_add, mul_one]
    exact L₀.add_mem (habs x hx y) hx
  have hmul : ∀ g g' : G, (∀ x : ℍ[ℚ, a, b], x ∈ L₀ → x * (χ g : ℍ[ℚ, a, b]) ∈ L₀) →
      (∀ x : ℍ[ℚ, a, b], x ∈ L₀ → x * (χ g' : ℍ[ℚ, a, b]) ∈ L₀) →
      ∀ x : ℍ[ℚ, a, b], x ∈ L₀ → x * (χ (g * g') : ℍ[ℚ, a, b]) ∈ L₀ := by
    intro g g' hg hg' x hx
    obtain ⟨y, hy⟩ := hρ.label_mul g g'
    rw [sub_eq_iff_eq_add] at hy
    rw [hy, mul_add, ← mul_assoc]
    exact L₀.add_mem (habs x hx y) (hg' _ (hg x hx))

  haveI hfin : Finite G := by
    set mΛ : Submodule ℤ ℍ[ℚ, a, b] := Submodule.span ℤ ((fun y : ℍ[ℚ, a, b] => (m : ℤ) • y) '' (Λ : Set ℍ[ℚ, a, b])) with hmΛdef
    have hidx : mΛ.toAddSubgroup.relIndex Λ.toAddSubgroup = m ^ 4 :=
      QuaternionAlgebra.IsOrder.relIndex_span_smul_eq_pow_four hΛ m hm0
    haveI : (mΛ.toAddSubgroup.addSubgroupOf Λ.toAddSubgroup).FiniteIndex :=
      ⟨by show mΛ.toAddSubgroup.relIndex Λ.toAddSubgroup ≠ 0; rw [hidx]; exact pow_ne_zero 4 hm0.ne'⟩
    haveI : Finite (↥Λ.toAddSubgroup ⧸ mΛ.toAddSubgroup.addSubgroupOf Λ.toAddSubgroup) :=
      AddSubgroup.finite_quotient_of_finiteIndex
    refine Finite.of_injective (fun g : G => ((⟨(χ g : ℍ[ℚ, a, b]), (χ g).2⟩ : ↥Λ.toAddSubgroup) :
      ↥Λ.toAddSubgroup ⧸ mΛ.toAddSubgroup.addSubgroupOf Λ.toAddSubgroup)) ?_
    intro g g' h
    rw [QuotientAddGroup.eq_iff_sub_mem, AddSubgroup.mem_addSubgroupOf] at h
    have h' : (χ g : ℍ[ℚ, a, b]) - (χ g' : ℍ[ℚ, a, b]) ∈ mΛ := h
    rw [hmΛdef, show (fun y : ℍ[ℚ, a, b] => (m : ℤ) • y) = ⇑((m : ℤ) • (LinearMap.id : ℍ[ℚ, a, b] →ₗ[ℤ] ℍ[ℚ, a, b])) from rfl,
      Submodule.span_image, Submodule.span_eq, Submodule.mem_map] at h'
    obtain ⟨y, hy, hyeq⟩ := h'
    apply hρ.label_injective g g'
    refine ⟨⟨y, hy⟩, ?_⟩
    rw [← hyeq]
    show ((m : ℤ) • y : ℍ[ℚ, a, b]) = ((m : ℕ) : ℚ) • y
    rw [Nat.cast_smul_eq_nsmul ℚ m y]
    exact natCast_zsmul y m

  have hpow : ∀ (g : G) (n : ℕ), (∀ x : ℍ[ℚ, a, b], x ∈ L₀ → x * (χ g : ℍ[ℚ, a, b]) ∈ L₀) →
      ∀ x : ℍ[ℚ, a, b], x ∈ L₀ → x * (χ (g ^ n) : ℍ[ℚ, a, b]) ∈ L₀ := by
    intro g n hg
    induction n with
    | zero => rw [pow_zero]; exact hone
    | succ n ih => rw [pow_succ]; exact hmul _ _ ih hg
  have hinv : ∀ g : G, (∀ x : ℍ[ℚ, a, b], x ∈ L₀ → x * (χ g : ℍ[ℚ, a, b]) ∈ L₀) →
      ∀ x : ℍ[ℚ, a, b], x ∈ L₀ → x * (χ g⁻¹ : ℍ[ℚ, a, b]) ∈ L₀ := by
    intro g hg
    have hn := orderOf_pos g
    have e : g⁻¹ = g ^ (orderOf g - 1) := by
      rw [eq_comm, ← mul_eq_one_iff_eq_inv, ← pow_succ, Nat.sub_add_cancel hn, pow_orderOf_eq_one]
    rw [e]
    exact hpow g _ hg
  refine ⟨{ carrier := {g : G | ∀ x : ℍ[ℚ, a, b], x ∈ L₀ → x * (χ g : ℍ[ℚ, a, b]) ∈ L₀}
            one_mem' := hone
            mul_mem' := fun {g g'} hg hg' => hmul g g' hg hg'
            inv_mem' := fun {g} hg => hinv g hg }, fun g => Iff.rfl⟩

end S_CerednikDrinfeld_QM_IsLevelTwistAction_exists_subgroup_mem_iff_forall_mul_mem
end P2MW
export P2MW.S_CerednikDrinfeld_QM_IsLevelTwistAction_exists_subgroup_mem_iff_forall_mul_mem (solution)
