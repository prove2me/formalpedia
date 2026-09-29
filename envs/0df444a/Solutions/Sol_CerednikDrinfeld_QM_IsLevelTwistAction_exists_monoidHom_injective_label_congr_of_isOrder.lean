-- Prove2me | solution 1 for CerednikDrinfeld.QM.IsLevelTwistAction.exists_monoidHom_injective_label_congr_of_isOrder
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/02ab5521-3f0d-5512-b203-6b76dddb85de

import Definitions.Def_CerednikDrinfeld_QMFineModuli
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_IsLevelTwistAction_exists_monoidHom_injective_label_congr_of_isOrder

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra
namespace LabelIso10

variable {a b : ℚ}

def Cong (Λ : Submodule ℤ ℍ[ℚ, a, b]) (m : ℕ) (x y : ℍ[ℚ, a, b]) : Prop :=
  ∃ t : ↥Λ, x - y = (m : ℚ) • (t : ℍ[ℚ, a, b])

variable {Λ : Submodule ℤ ℍ[ℚ, a, b]} {m : ℕ}

theorem Cong.refl (x : ℍ[ℚ, a, b]) : Cong Λ m x x := ⟨0, by simp⟩

theorem Cong.symm {x y : ℍ[ℚ, a, b]} (h : Cong Λ m x y) : Cong Λ m y x := by
  obtain ⟨t, ht⟩ := h
  refine ⟨-t, ?_⟩
  rw [Submodule.coe_neg, smul_neg, ← ht]; abel

theorem Cong.trans {x y z : ℍ[ℚ, a, b]} (h : Cong Λ m x y) (h' : Cong Λ m y z) : Cong Λ m x z := by
  obtain ⟨t, ht⟩ := h; obtain ⟨t', ht'⟩ := h'
  refine ⟨t + t', ?_⟩
  rw [Submodule.coe_add, smul_add, ← ht, ← ht']; abel

theorem Cong.mul (hΛ : IsOrder Λ) {x x' y y' : ℍ[ℚ, a, b]} (hx : x ∈ Λ) (hy' : y' ∈ Λ)
    (h : Cong Λ m x x') (h' : Cong Λ m y y') : Cong Λ m (x * y) (x' * y') := by
  obtain ⟨t, ht⟩ := h; obtain ⟨t', ht'⟩ := h'
  refine ⟨⟨x * t' + t * y', Λ.add_mem (hΛ.mul_mem hx t'.2) (hΛ.mul_mem t.2 hy')⟩, ?_⟩
  have e : x * y - x' * y' = x * (y - y') + (x - x') * y' := by rw [mul_sub, sub_mul]; abel
  rw [e, ht, ht']
  simp only [Submodule.coe_mk, smul_add, mul_smul_comm, smul_mul_assoc]

end LabelIso10

open LabelIso10 in

theorem solution
    {a b : ℚ} (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsOrder Λ) (N m : ℕ)
    {B₀ : Type} [CommRing B₀] {M₀ : Scheme.{0}} {πM₀ : M₀ ⟶ Spec (CommRingCat.of B₀)}
    {ptF₀ : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B₀)),
      FakeEllipticCurve.WithFullLevel Λ N m S → SchemeHomOver s πM₀}
    {G₀ : Type} [Group G₀] {ρ₀ : G₀ →* Aut M₀} {χ₀ : G₀ → ↥Λ} (hρ₀ : IsLevelTwistAction Λ N m M₀ πM₀ ptF₀ G₀ ρ₀ χ₀)
    {𝒪 : Type} [CommRing 𝒪] {M : Scheme.{0}} {πM : M ⟶ Spec (CommRingCat.of 𝒪)}
    {ptF : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)),
      FakeEllipticCurve.WithFullLevel Λ N m S → SchemeHomOver s πM}
    {G : Type} [Group G] {ρ : G →* Aut M} {χ : G → ↥Λ} (hρ : IsLevelTwistAction Λ N m M πM ptF G ρ χ) :
    ∃ ψ : G →* G₀, Function.Injective ψ ∧
      ∀ g : G, ∃ y : ↥Λ, (χ₀ (ψ g) : ℍ[ℚ, a, b]) - (χ g : ℍ[ℚ, a, b]) = (m : ℚ) • (y : ℍ[ℚ, a, b]) := by
  classical

  have hex : ∀ g : G, ∃ g₀ : G₀, Cong Λ m (χ₀ g₀ : ℍ[ℚ, a, b]) (χ g : ℍ[ℚ, a, b]) := by
    intro g
    have h1 : Cong Λ m ((χ g : ℍ[ℚ, a, b]) * (χ g⁻¹ : ℍ[ℚ, a, b])) 1 := by
      obtain ⟨y, hy⟩ := hρ.label_mul g g⁻¹
      obtain ⟨y₁, hy₁⟩ := hρ.label_one
      rw [mul_inv_cancel] at hy
      exact (Cong.symm ⟨y, hy⟩).trans ⟨y₁, hy₁⟩
    have h2 : Cong Λ m ((χ g⁻¹ : ℍ[ℚ, a, b]) * (χ g : ℍ[ℚ, a, b])) 1 := by
      obtain ⟨y, hy⟩ := hρ.label_mul g⁻¹ g
      obtain ⟨y₁, hy₁⟩ := hρ.label_one
      rw [inv_mul_cancel] at hy
      exact (Cong.symm ⟨y, hy⟩).trans ⟨y₁, hy₁⟩
    obtain ⟨g₀, y, hy⟩ := hρ₀.label_surjective (χ g) (χ g⁻¹) h1 h2
    exact ⟨g₀, y, hy⟩
  choose ψf hψf using hex

  have hone : ψf 1 = 1 := by
    apply hρ₀.label_injective
    obtain ⟨y₁, hy₁⟩ := hρ.label_one
    obtain ⟨y₀, hy₀⟩ := hρ₀.label_one
    exact ((hψf 1).trans ⟨y₁, hy₁⟩).trans (Cong.symm ⟨y₀, hy₀⟩)
  have hmul : ∀ g g' : G, ψf (g * g') = ψf g * ψf g' := by
    intro g g'
    apply hρ₀.label_injective
    obtain ⟨y, hy⟩ := hρ.label_mul g g'
    obtain ⟨y₀, hy₀⟩ := hρ₀.label_mul (ψf g) (ψf g')
    have hc : Cong Λ m ((χ g : ℍ[ℚ, a, b]) * (χ g' : ℍ[ℚ, a, b]))
        ((χ₀ (ψf g) : ℍ[ℚ, a, b]) * (χ₀ (ψf g') : ℍ[ℚ, a, b])) :=
      Cong.mul hΛ (χ g).2 (χ₀ (ψf g')).2 (hψf g).symm (hψf g').symm
    exact (((hψf (g * g')).trans ⟨y, hy⟩).trans hc).trans (Cong.symm ⟨y₀, hy₀⟩)
  refine ⟨{ toFun := ψf, map_one' := hone, map_mul' := hmul }, ?_, ?_⟩
  · intro g g' hgg'
    apply hρ.label_injective
    have : ψf g = ψf g' := hgg'
    exact ((hψf g).symm.trans (by rw [this]; exact Cong.refl _)).trans (hψf g')
  · intro g
    exact hψf g

end S_CerednikDrinfeld_QM_IsLevelTwistAction_exists_monoidHom_injective_label_congr_of_isOrder
end P2MW
export P2MW.S_CerednikDrinfeld_QM_IsLevelTwistAction_exists_monoidHom_injective_label_congr_of_isOrder (solution)
