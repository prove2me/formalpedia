-- Prove2me | solution 1 for Formalism.L2.G.Cmp.Fib.cls_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:12:00.776779+00:00
-- url     : https://prove2.me/submissions/c5a4bdb1-52b3-4ab3-9236-646edcfc9e3e

import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_ComparisonMaps_ClsFib
import Theorems.Thm_Formalism_L2_G_Cmp_Fib_mk_eq_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.L2 Formalism.L2.G Formalism.L2.G.Cmp
open Formalism.UG
open Formalism.L2.G.Cmp.Fib
variable {G Gp : Type} [Group G] [Group Gp] {K K' : Subgroup G} {Kp : Subgroup Gp} (X : Fib K K' Kp) (H : Subgroup G)
variable (y : ClassSet H K' → G) (hy : ∀ i, mkC H K' (y i) = i) (hp : ∀ i, X.pr (y i) = 1)
include hy hp
namespace Formalism.L2.G.Cmp.Fib
theorem _root_.solution (i i' : ClassSet H K') (g g' : Gp) :
    mkC H K (y i * X.j g) = mkC H K (y i' * X.j g') ↔
      i = i' ∧ ∃ γ ∈ H, (y i)⁻¹ * γ * y i ∈ K' ∧ g'⁻¹ * (X.pr γ * g) ∈ Kp := by
  rw [mk_eq_iff]
  constructor
  · rintro ⟨h, hh, κ, hκ, he⟩
    have hκ' := (X.K_iff κ).1 hκ
    have hi : i = i' := by
      rw [← hy i, ← hy i', mk_eq_iff]
      refine ⟨h, hh, X.j g * κ * (X.j g')⁻¹,
        K'.mul_mem (K'.mul_mem (X.j_mem g) hκ'.1) (K'.inv_mem (X.j_mem g')), ?_⟩
      calc y i' = (y i' * X.j g') * (X.j g')⁻¹ := by group
        _ = h * (y i * X.j g) * κ * (X.j g')⁻¹ := by rw [he]
        _ = h * y i * (X.j g * κ * (X.j g')⁻¹) := by group
    subst hi
    have hh' : h = (y i * X.j g') * κ⁻¹ * (y i * X.j g)⁻¹ := by rw [he]; group
    have hz : (y i)⁻¹ * h * y i = X.j g' * κ⁻¹ * (X.j g)⁻¹ := by rw [hh']; group
    refine ⟨rfl, h, hh, ?_, ?_⟩
    · rw [hz]
      exact K'.mul_mem (K'.mul_mem (X.j_mem _) (K'.inv_mem hκ'.1)) (K'.inv_mem (X.j_mem _))
    · rw [hh']
      simp only [map_mul, map_inv, X.pr_j, hp]
      convert Kp.inv_mem hκ'.2 using 1
      group
  · rintro ⟨rfl, γ, hγ, hz, hg⟩
    refine ⟨γ, hγ, (y i * X.j g)⁻¹ * γ⁻¹ * (y i * X.j g'), ?_, by group⟩
    rw [X.K_iff]
    have e : (y i * X.j g)⁻¹ * γ⁻¹ * (y i * X.j g') =
        (X.j g)⁻¹ * ((y i)⁻¹ * γ * y i)⁻¹ * X.j g' := by group
    rw [e]
    refine ⟨K'.mul_mem (K'.mul_mem (K'.inv_mem (X.j_mem _)) (K'.inv_mem hz)) (X.j_mem _), ?_⟩
    simp only [map_mul, map_inv, X.pr_j, hp]
    convert Kp.inv_mem hg using 1
    group
end Formalism.L2.G.Cmp.Fib
