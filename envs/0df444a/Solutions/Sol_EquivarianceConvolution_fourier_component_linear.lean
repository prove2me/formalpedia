-- Prove2me | solution 1 for EquivarianceConvolution.fourier_component_linear
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-24T07:28:54.103157+00:00
-- url     : https://prove2.me/submissions/8e403f86-0247-4fc1-b946-72bde82f745e

import Mathlib
import Definitions.Def_EquivarianceConvolution_Basic

universe u

namespace EquivarianceConvolution

open scoped BigOperators

theorem ec2_card_fiber {G : Type*} [Group G] [Fintype G] (H : Subgroup G) (a : G)
    [DecidablePred fun g : G => (g : G ⧸ H) = (a : G ⧸ H)] :
    (Finset.univ.filter fun g : G => (g : G ⧸ H) = (a : G ⧸ H)).card = Nat.card H := by
  rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
  have h := QuotientGroup.card_preimage_mk H {(a : G ⧸ H)}
  rw [Nat.card_unique (α := (({(a : G ⧸ H)} : Set (G ⧸ H)) : Type _)), mul_one] at h
  exact h

end EquivarianceConvolution

open EquivarianceConvolution in
theorem solution {G : Type*} [Group G] [Fintype G] (H K : Subgroup G)
    (φ : (G ⧸ H → ℂ) →ₗ[ℂ] (G ⧸ K → ℂ)) (hφ : IsEquivariantMap G ⇑φ) {n : ℕ}
    (ρ : G →* Matrix (Fin n) (Fin n) ℂ) (hρ : IsIrrep ρ) :
    ∃ Φ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin n) (Fin n) ℂ,
      ∀ f : G ⧸ H → ℂ, groupFourier ρ (liftQ (φ f)) = Φ (groupFourier ρ (liftQ f)) := by
  classical
  set δ : G ⧸ H → ℂ := fun x => if x = ((1 : G) : G ⧸ H) then 1 else 0 with hδ
  set ψ : G ⧸ K → ℂ := φ δ with hψ
  set c : ℂ := ((Nat.card H : ℕ) : ℂ)⁻¹ with hc
  have hH : ((Nat.card H : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (Nat.card_pos (α := H)).ne'
  have hdec : ∀ f : G ⧸ H → ℂ, f = c • ∑ g : G, f (g : G ⧸ H) • translateFun g δ := by
    intro f; funext x
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective x
    simp only [Pi.smul_apply, Finset.sum_apply, smul_eq_mul]
    have key : ∀ g : G, f (g : G ⧸ H) * translateFun g δ (a : G ⧸ H) =
        if (g : G ⧸ H) = (a : G ⧸ H) then f (a : G ⧸ H) else 0 := by
      intro g
      show f (g : G ⧸ H) * δ ((g⁻¹ * a : G) : G ⧸ H) = _
      simp only [hδ]
      by_cases hg : (g : G ⧸ H) = (a : G ⧸ H)
      · have : ((g⁻¹ * a : G) : G ⧸ H) = ((1 : G) : G ⧸ H) := by
          rw [QuotientGroup.eq] at hg ⊢; simpa using H.inv_mem hg
        simp [hg, this]
      · have : ((g⁻¹ * a : G) : G ⧸ H) ≠ ((1 : G) : G ⧸ H) := by
          intro h; apply hg; rw [QuotientGroup.eq] at h ⊢; simpa using H.inv_mem h
        simp [hg, this]
    rw [Finset.sum_congr rfl (fun g _ => key g), Finset.sum_ite, Finset.sum_const_zero, add_zero,
      Finset.sum_const, ec2_card_fiber, nsmul_eq_mul, hc]
    field_simp
  have hlift : ∀ (f : G ⧸ H → ℂ) (u : G),
      liftQ (φ f) u = c * ∑ g : G, f (g : G ⧸ H) * ψ ((g⁻¹ * u : G) : G ⧸ K) := by
    intro f u
    conv_lhs => rw [hdec f]
    simp only [map_smul, map_sum, liftQ, Pi.smul_apply, Finset.sum_apply, smul_eq_mul]
    congr 1
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [hφ]
    rfl
  refine ⟨LinearMap.mulRight ℂ (c • ∑ v : G, ψ (v : G ⧸ K) • ρ v), fun f => ?_⟩
  rw [LinearMap.mulRight_apply]
  unfold groupFourier
  simp only [hlift]
  calc ∑ u : G, (c * ∑ g : G, f (g : G ⧸ H) * ψ ((g⁻¹ * u : G) : G ⧸ K)) • ρ u
      = ∑ g : G, ∑ v : G, (c * (f (g : G ⧸ H) * ψ (v : G ⧸ K))) • (ρ g * ρ v) := by
        simp_rw [Finset.mul_sum, Finset.sum_smul]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun g _ => ?_
        rw [← Equiv.sum_comp (Equiv.mulLeft g)]
        refine Finset.sum_congr rfl fun v _ => ?_
        simp [map_mul]
    _ = (∑ u : G, liftQ f u • ρ u) * (c • ∑ v : G, ψ (v : G ⧸ K) • ρ v) := by
        simp_rw [Finset.smul_sum, Finset.sum_mul, Finset.mul_sum]
        refine Finset.sum_congr rfl fun g _ => ?_
        refine Finset.sum_congr rfl fun v _ => ?_
        rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_smul, smul_smul, smul_smul]
        congr 1
        show c * (f (g : G ⧸ H) * ψ (v : G ⧸ K)) = f (g : G ⧸ H) * c * ψ (v : G ⧸ K)
        ring
