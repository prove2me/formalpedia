-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.U0.norm_formula
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:16:49.692803+00:00
-- url     : https://prove2.me/submissions/d5ad9daf-903e-4418-98a1-7b303bc65a95

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsIsomFrame
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AddMulInvMem
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsNormRepresentation
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_U0_Dv_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.U0
open WA
variable {K : Type*} [Field K] [StarRing K]
variable {S : Subring K} {π : K}
variable {V : Type*} [AddCommGroup V] [Module K V]
namespace Formalism.HermitianLattices.Ext.L3.U0
theorem _root_.solution {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) {y w : V} {a u ρ : K}
    (hy : h y y = star a * a * u) (hu : star u = u)
    (hρ : ρ * (h w y - u * a) + star (ρ * (h w y - u * a)) = u - h w w) :
    h (ρ • y + w) (ρ • y + w) = u * (star (1 + ρ * a) * (1 + ρ * a)) := by
  have hyw : h y w = star (h w y) := (hs.eq w y).symm
  simp only [map_add, LinearMap.add_apply, map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, hy, hyw,
    starRingEnd_apply, RingHom.id_apply]
  simp only [star_mul', star_sub, hu, star_add, star_one] at hρ ⊢
  linear_combination hρ
end Formalism.HermitianLattices.Ext.L3.U0
