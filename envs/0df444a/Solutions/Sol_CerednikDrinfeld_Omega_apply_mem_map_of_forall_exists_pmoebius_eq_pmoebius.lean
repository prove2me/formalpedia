-- Prove2me | solution 1 for CerednikDrinfeld.Omega.apply_mem_map_of_forall_exists_pmoebius_eq_pmoebius
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/de26eef9-64ec-5930-a449-967551c91dbb

import Definitions.Def_CerednikDrinfeld_DrinfeldUpperHalfPlane
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_Omega_apply_mem_map_of_forall_exists_pmoebius_eq_pmoebius

set_option autoImplicit false

open scoped MatrixGroups
p2m_open "CerednikDrinfeld P2MW.S_CerednikDrinfeld_Omega_apply_mem_map_of_forall_exists_pmoebius_eq_pmoebius.CerednikDrinfeld CerednikDrinfeld.Omega P2MW.S_CerednikDrinfeld_Omega_apply_mem_map_of_forall_exists_pmoebius_eq_pmoebius.CerednikDrinfeld.Omega"

namespace CerednikDrinfeld
p2m_export "CerednikDrinfeld" "Omega.pmoebius Omega.upperHalfPlane"
namespace Omega
p2m_export "CerednikDrinfeld.Omega" "moebius pmoebius pmoebius_mk upperHalfPlane moebius_denom_ne_zero_of_mem pmoebius_one pmoebius_mul"
namespace OrbitMem
p2m_open "CerednikDrinfeld.Omega CerednikDrinfeld"

theorem eq_one_of_pmoebius_eq_self_three (K₀ : Type) [Field K₀] {K : Type} [Field K] [Algebra K₀ K] [DecidableEq K]
    (η : PGL(2, K₀)) {z₁ z₂ z₃ : K}
    (hz₁ : z₁ ∈ upperHalfPlane K₀ K) (hz₂ : z₂ ∈ upperHalfPlane K₀ K) (hz₃ : z₃ ∈ upperHalfPlane K₀ K)
    (h12 : z₁ ≠ z₂) (h13 : z₁ ≠ z₃) (h23 : z₂ ≠ z₃)
    (h₁ : pmoebius K₀ η z₁ = z₁) (h₂ : pmoebius K₀ η z₂ = z₂) (h₃ : pmoebius K₀ η z₃ = z₃) : η = 1 := by
  induction η using Matrix.ProjGenLinGroup.induction_on with
  | _ M =>
  have quad : ∀ {z : K}, z ∈ upperHalfPlane K₀ K → pmoebius K₀ (Matrix.ProjGenLinGroup.mk M) z = z →
      algebraMap K₀ K (M 1 0) * z ^ 2 + (algebraMap K₀ K (M 1 1) - algebraMap K₀ K (M 0 0)) * z
        - algebraMap K₀ K (M 0 1) = 0 := by
    intro z hz h
    have hden := moebius_denom_ne_zero_of_mem K₀ hz M
    rw [pmoebius_mk K₀ M z hden, moebius, div_eq_iff hden] at h
    linear_combination (-1 : K) * h
  have e₁ := quad hz₁ h₁
  have e₂ := quad hz₂ h₂
  have e₃ := quad hz₃ h₃
  have s12 : (z₁ - z₂) * (algebraMap K₀ K (M 1 0) * (z₁ + z₂) +
      (algebraMap K₀ K (M 1 1) - algebraMap K₀ K (M 0 0))) = 0 := by
    linear_combination e₁ - e₂
  have s13 : (z₁ - z₃) * (algebraMap K₀ K (M 1 0) * (z₁ + z₃) +
      (algebraMap K₀ K (M 1 1) - algebraMap K₀ K (M 0 0))) = 0 := by
    linear_combination e₁ - e₃
  have t12 := (mul_eq_zero.1 s12).resolve_left (sub_ne_zero.2 h12)
  have t13 := (mul_eq_zero.1 s13).resolve_left (sub_ne_zero.2 h13)
  have hC : algebraMap K₀ K (M 1 0) * (z₂ - z₃) = 0 := by linear_combination t12 - t13
  have hC0 : algebraMap K₀ K (M 1 0) = 0 := (mul_eq_zero.1 hC).resolve_right (sub_ne_zero.2 h23)
  have hDA : algebraMap K₀ K (M 1 1) - algebraMap K₀ K (M 0 0) = 0 := by
    linear_combination t12 - (z₁ + z₂) * hC0
  have hB : algebraMap K₀ K (M 0 1) = 0 := by
    linear_combination (-1 : K) * e₁ + z₁ ^ 2 * hC0 + z₁ * hDA
  have inj := (algebraMap K₀ K).injective
  have m10 : M 1 0 = 0 := inj (by rw [map_zero]; exact hC0)
  have m11 : M 1 1 = M 0 0 := inj (sub_eq_zero.1 hDA)
  have m01 : M 0 1 = 0 := inj (by rw [map_zero]; exact hB)
  have m00 : M 0 0 ≠ 0 := by
    intro h0
    apply M.det_ne_zero
    rw [Matrix.det_fin_two, m10, m01, h0]
    ring
  have hM : M = Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.mk0 (M 0 0) m00) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.GeneralLinearGroup.scalar, m10, m01, m11]
  rw [hM]
  exact Matrix.ProjGenLinGroup.mk_scalar _

end CerednikDrinfeld.Omega.OrbitMem

theorem solution
    (K₀ : Type) [Field K₀] (K : Type) [Field K] [Algebra K₀ K] [DecidableEq K]
    (hunc : ¬ (Omega.upperHalfPlane K₀ K).Countable)
    (G : Type) [Group G] (ρ : G →* PGL(2, K₀))
    (Δ : Subgroup G) (hcount : Countable ↥(Δ.map ρ))
    (g : G)
    (hg : ∀ z ∈ Omega.upperHalfPlane K₀ K, ∃ δ ∈ Δ, Omega.pmoebius K₀ (ρ g) z = Omega.pmoebius K₀ (ρ δ) z) :
    ρ g ∈ Δ.map ρ := by
  classical
  haveI : Countable ↥(Δ.map ρ) := hcount

  let F : ↥(Δ.map ρ) → Set K := fun δ =>
    {z | z ∈ Omega.upperHalfPlane K₀ K ∧ Omega.pmoebius K₀ (ρ g) z = Omega.pmoebius K₀ (δ : PGL(2, K₀)) z}
  have hcov : Omega.upperHalfPlane K₀ K ⊆ ⋃ δ, F δ := by
    intro z hz
    obtain ⟨δ, hδ, h⟩ := hg z hz
    exact Set.mem_iUnion.2 ⟨⟨ρ δ, Subgroup.mem_map_of_mem ρ hδ⟩, hz, h⟩

  obtain ⟨δ, hδ⟩ : ∃ δ : ↥(Δ.map ρ), ¬ (F δ).Countable := by
    by_contra hall
    push Not at hall
    exact hunc ((Set.countable_iUnion hall).mono hcov)
  have hinf : (F δ).Infinite := fun hfin => hδ hfin.countable
  obtain ⟨t, ht, hcard⟩ := hinf.exists_subset_card_eq 3
  obtain ⟨z₁, z₂, z₃, h12, h13, h23, rfl⟩ := Finset.card_eq_three.1 hcard
  have hz₁ : z₁ ∈ F δ := ht (by simp)
  have hz₂ : z₂ ∈ F δ := ht (by simp)
  have hz₃ : z₃ ∈ F δ := ht (by simp)

  have hfix : ∀ {z : K}, z ∈ F δ → Omega.pmoebius K₀ ((δ : PGL(2, K₀))⁻¹ * ρ g) z = z := by
    rintro z ⟨hz, h⟩
    rw [pmoebius_mul K₀ hz, h, ← pmoebius_mul K₀ hz, inv_mul_cancel, pmoebius_one]
  have hη : (δ : PGL(2, K₀))⁻¹ * ρ g = 1 :=
    OrbitMem.eq_one_of_pmoebius_eq_self_three K₀ _ hz₁.1 hz₂.1 hz₃.1 h12 h13 h23 (hfix hz₁) (hfix hz₂) (hfix hz₃)
  have hg' : ρ g = (δ : PGL(2, K₀)) := (inv_mul_eq_one.1 hη).symm
  rw [hg']
  exact δ.2

end S_CerednikDrinfeld_Omega_apply_mem_map_of_forall_exists_pmoebius_eq_pmoebius
end P2MW
export P2MW.S_CerednikDrinfeld_Omega_apply_mem_map_of_forall_exists_pmoebius_eq_pmoebius (solution)
