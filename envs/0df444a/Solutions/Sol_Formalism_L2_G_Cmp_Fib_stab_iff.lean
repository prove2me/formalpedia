-- Prove2me | solution 1 for Formalism.L2.G.Cmp.Fib.stab_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T09:58:10.424222+00:00
-- url     : https://prove2.me/submissions/2d2ba0ca-432f-4b26-befd-ed55290fdb36

import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_ComparisonMaps_ClsFib

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
include hp
namespace Formalism.L2.G.Cmp.Fib
theorem _root_.solution (i : ClassSet H K') (g : Gp) (γ : G) :
    (y i * X.j g)⁻¹ * γ * (y i * X.j g) ∈ K ↔ (y i)⁻¹ * γ * y i ∈ K' ∧ g⁻¹ * (X.pr γ * g) ∈ Kp := by
  have hz : (y i * X.j g)⁻¹ * γ * (y i * X.j g) = (X.j g)⁻¹ * ((y i)⁻¹ * γ * y i) * X.j g := by
    group
  rw [hz, X.K_iff]
  have hjg := X.j_mem g
  have h1 : (X.j g)⁻¹ * ((y i)⁻¹ * γ * y i) * X.j g ∈ K' ↔ (y i)⁻¹ * γ * y i ∈ K' := by
    constructor
    · intro h
      have h2 := K'.mul_mem (K'.mul_mem hjg h) (K'.inv_mem hjg)
      have e : X.j g * ((X.j g)⁻¹ * ((y i)⁻¹ * γ * y i) * X.j g) * (X.j g)⁻¹ =
          (y i)⁻¹ * γ * y i := by group
      rwa [e] at h2
    · intro h
      exact K'.mul_mem (K'.mul_mem (K'.inv_mem hjg) h) hjg
  rw [h1]
  simp only [map_mul, map_inv, X.pr_j, hp, inv_one, one_mul, mul_one, mul_assoc]
end Formalism.L2.G.Cmp.Fib
