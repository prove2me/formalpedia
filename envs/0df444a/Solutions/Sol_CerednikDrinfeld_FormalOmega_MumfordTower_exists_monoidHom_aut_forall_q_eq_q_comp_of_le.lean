-- Prove2me | solution 1 for CerednikDrinfeld.FormalOmega.MumfordTower.exists_monoidHom_aut_forall_q_eq_q_comp_of_le
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/947005da-d2c6-5398-b0a9-c8d9c64ae263

import Definitions.Def_CerednikDrinfeld_MumfordTower
import Definitions.Def_CerednikDrinfeld_BruhatTitsTree
import Theorems.Thm_CerednikDrinfeld_FormalOmega_MumfordTower_exists_action_forall_q_eq_q_comp
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_FormalOmega_MumfordTower_exists_monoidHom_aut_forall_q_eq_q_comp_of_le

set_option autoImplicit false

open scoped TensorProduct MatrixGroups
p2m_open "CategoryTheory AlgebraicGeometry LT.LatticeTree CerednikDrinfeld P2MW.S_CerednikDrinfeld_FormalOmega_MumfordTower_exists_monoidHom_aut_forall_q_eq_q_comp_of_le.CerednikDrinfeld CerednikDrinfeld.FormalOmega P2MW.S_CerednikDrinfeld_FormalOmega_MumfordTower_exists_monoidHom_aut_forall_q_eq_q_comp_of_le.CerednikDrinfeld.FormalOmega"

namespace CerednikDrinfeld
p2m_export "CerednikDrinfeld" "FormalOmega.MumfordTower FormalOmega.MumfordTower.exists_action_forall_q_eq_q_comp"
namespace FormalOmega
p2m_export "CerednikDrinfeld.FormalOmega" "MumfordTower Omega DeligneDatum DeligneDatum.IsPullback MumfordTower.exists_action_forall_q_eq_q_comp"
namespace TowerAction
p2m_open "CerednikDrinfeld.FormalOmega CerednikDrinfeld"

theorem conj_mem_iff_of_le_of_normal {G : Type} [Group G] {K₀ : Type} [Field K₀]
    (Γ : Subgroup G) (ρ : G →* PGL(2, K₀)) (N : Subgroup (PGL(2, K₀)))
    (hNle : N ≤ Γ.map ρ) (hNnorm : (N.subgroupOf (Γ.map ρ)).Normal) (γ : ↥Γ) (x : PGL(2, K₀)) :
    x ∈ N ↔ ρ (γ : G) * x * (ρ (γ : G))⁻¹ ∈ N := by
  have key : ∀ (δ : ↥Γ) (y : PGL(2, K₀)), y ∈ N → ρ (δ : G) * y * (ρ (δ : G))⁻¹ ∈ N := by
    intro δ y hy
    have hy' : (⟨y, hNle hy⟩ : ↥(Γ.map ρ)) ∈ N.subgroupOf (Γ.map ρ) := Subgroup.mem_subgroupOf.mpr hy
    have := hNnorm.conj_mem _ hy' ⟨ρ (δ : G), Subgroup.mem_map_of_mem ρ δ.2⟩
    exact Subgroup.mem_subgroupOf.mp this
  refine ⟨key γ x, fun h => ?_⟩
  have := key γ⁻¹ _ h
  simpa [mul_assoc] using this

theorem core (𝒪 : Type) [CommRing 𝒪] (π : 𝒪) (K₀ : Type) [Field K₀] [Algebra 𝒪 K₀] (r : ℕ)
    (g₁ : Matrix.GeneralLinearGroup (Fin 2) K₀)
    (G : Type) [Group G] (σ : G →* Matrix.GeneralLinearGroup (Fin 2) K₀) (Γ : Subgroup G)
    (ρ : G →* PGL(2, K₀)) (hρ : ∀ g : G, ρ g = Matrix.ProjGenLinGroup.mk (σ g))
    (N : Subgroup (PGL(2, K₀)))
    (hnorm : ∀ (γ : ↥Γ) (x : PGL(2, K₀)), x ∈ N ↔ ρ (γ : G) * x * (ρ (γ : G))⁻¹ ∈ N)
    (D : MumfordTower 𝒪 π K₀ r g₁ N) :
    ∃ act : ∀ n : ℕ, ↥Γ →* Aut (D.Z n),
      (∀ (n : ℕ) (γ : ↥Γ), (act n γ).hom ≫ D.zb n = D.zb n) ∧
      (∀ (n : ℕ) (γ : ↥Γ), D.zt n ≫ (act (n + 1) γ).hom = (act n γ).hom ≫ D.zt n) ∧
      (∀ (n : ℕ) (γ : ↥Γ), ρ (γ : G) ∈ N → (act n γ).hom = 𝟙 (D.Z n)) ∧
      (∀ (n : ℕ) (γ : ↥Γ) (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : (algebraMap 𝒪 B π) ^ (n + 1) = 0)
        (P P' : (Omega K₀ π).obj B), DeligneDatum.IsPullback (K := K₀) (π := π) B (σ (γ : G))⁻¹ P P' →
        D.q n B hB P' = D.q n B hB P ≫ (act n γ).hom) := by
  obtain ⟨a, hzb, hzt, hq, huniq, htriv, hmul⟩ :=
    CerednikDrinfeld.FormalOmega.MumfordTower.exists_action_forall_q_eq_q_comp 𝒪 π K₀ r g₁ N D

  have hg : ∀ γ : ↥Γ, ∀ x : PGL(2, K₀),
      x ∈ N ↔ Matrix.ProjGenLinGroup.mk (σ (γ : G)) * x * (Matrix.ProjGenLinGroup.mk (σ (γ : G)))⁻¹ ∈ N := by
    intro γ x; rw [← hρ]; exact hnorm γ x

  have a_congr : ∀ (g g' : Matrix.GeneralLinearGroup (Fin 2) K₀) (hg : _) (hg' : _) (n : ℕ), g = g' →
      (a g hg n).hom = (a g' hg' n).hom := by
    intro g g' hg hg' n e; subst e; rfl
  refine ⟨fun n =>
    { toFun := fun γ => a (σ (γ : G)) (hg γ) n
      map_one' := ?_
      map_mul' := ?_ }, ?_, ?_, ?_, ?_⟩
  ·
    apply Iso.ext
    have h1 : Matrix.ProjGenLinGroup.mk (σ ((1 : ↥Γ) : G)) ∈ N := by
      rw [← hρ, OneMemClass.coe_one, map_one]; exact one_mem N
    exact htriv _ (hg 1) n h1
  ·
    intro γ δ
    apply Iso.ext
    have e : σ ((γ * δ : ↥Γ) : G) = σ (γ : G) * σ (δ : G) := by rw [Subgroup.coe_mul, map_mul]
    have hgg' : ∀ x : PGL(2, K₀), x ∈ N ↔ Matrix.ProjGenLinGroup.mk (σ (γ : G) * σ (δ : G)) * x *
        (Matrix.ProjGenLinGroup.mk (σ (γ : G) * σ (δ : G)))⁻¹ ∈ N := by
      intro x; rw [← e]; exact hg (γ * δ) x
    rw [a_congr _ _ (hg (γ * δ)) hgg' n e, hmul _ (hg γ) _ (hg δ) hgg' n]
    rfl
  · intro n γ; exact hzb _ (hg γ) n
  · intro n γ; exact hzt _ (hg γ) n
  · intro n γ hN
    have : Matrix.ProjGenLinGroup.mk (σ (γ : G)) ∈ N := by rw [← hρ]; exact hN
    exact htriv _ (hg γ) n this
  · intro n γ B _ _ hB P P' hP
    exact hq _ (hg γ) n B hB P P' hP

end CerednikDrinfeld.FormalOmega.TowerAction

theorem solution
    (𝒪 : Type) [CommRing 𝒪] (π : 𝒪) (K₀ : Type) [Field K₀] [Algebra 𝒪 K₀] (r : ℕ)
    (g₁ : Matrix.GeneralLinearGroup (Fin 2) K₀)
    (G : Type) [Group G] (σ : G →* Matrix.GeneralLinearGroup (Fin 2) K₀) (Γ : Subgroup G)
    (ρ : G →* PGL(2, K₀)) (hρ : ∀ g : G, ρ g = Matrix.ProjGenLinGroup.mk (σ g))
    (N : Subgroup (PGL(2, K₀))) (hNle : N ≤ Γ.map ρ) (hNnorm : (N.subgroupOf (Γ.map ρ)).Normal)
    (D : MumfordTower 𝒪 π K₀ r g₁ N) :
    ∃ act : ∀ n : ℕ, ↥Γ →* Aut (D.Z n),

      (∀ (n : ℕ) (γ : ↥Γ), (act n γ).hom ≫ D.zb n = D.zb n) ∧

      (∀ (n : ℕ) (γ : ↥Γ), D.zt n ≫ (act (n + 1) γ).hom = (act n γ).hom ≫ D.zt n) ∧

      (∀ (n : ℕ) (γ : ↥Γ), ρ (γ : G) ∈ N → (act n γ).hom = 𝟙 (D.Z n)) ∧

      (∀ (n : ℕ) (γ : ↥Γ) (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : (algebraMap 𝒪 B π) ^ (n + 1) = 0)
        (P P' : (Omega K₀ π).obj B), DeligneDatum.IsPullback (K := K₀) (π := π) B (σ (γ : G))⁻¹ P P' →
        D.q n B hB P' = D.q n B hB P ≫ (act n γ).hom) :=
  CerednikDrinfeld.FormalOmega.TowerAction.core 𝒪 π K₀ r g₁ G σ Γ ρ hρ N
    (CerednikDrinfeld.FormalOmega.TowerAction.conj_mem_iff_of_le_of_normal Γ ρ N hNle hNnorm) D

end S_CerednikDrinfeld_FormalOmega_MumfordTower_exists_monoidHom_aut_forall_q_eq_q_comp_of_le
end P2MW
export P2MW.S_CerednikDrinfeld_FormalOmega_MumfordTower_exists_monoidHom_aut_forall_q_eq_q_comp_of_le (solution)
