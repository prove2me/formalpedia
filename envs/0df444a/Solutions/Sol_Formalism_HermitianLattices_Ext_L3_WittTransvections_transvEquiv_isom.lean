-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.WittTransvections.transvEquiv_isom
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:27:19.019626+00:00
-- url     : https://prove2.me/submissions/f574f563-551d-42d5-ae3b-ac5dd5fb0c81

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_FiniteDimensionalOfOrtho
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsIsomMapOfEq
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_WittTransvections_transvEquiv_apply
import Theorems.Thm_Formalism_H_dualEquiv_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.H.dualEquiv_apply



set_option autoImplicit false
open NumberField Module
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3
open Formalism.HermitianLattices.Ext.L3.WittTransvections
variable {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V]
namespace Formalism.HermitianLattices.Ext.L3.WittTransvections
theorem _root_.solution {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (u : V) {ξ : K}
    (hξ : ξ + star ξ = ξ * star ξ * h u u) (v w : V) :
    h (transvEquiv h u hξ v) (transvEquiv h u hξ w) = h v w := by
  rw [transvEquiv_apply, transvEquiv_apply]
  have h1 : star (h u v) = h v u := by rw [← starRingEnd_apply]; exact hs.eq u v
  simp only [map_sub, LinearMap.map_smulₛₗ, LinearMap.sub_apply, LinearMap.smul_apply, map_smul, smul_eq_mul,
    map_mul, starRingEnd_apply, star_mul', h1]
  linear_combination (-(h v u * h u w)) * hξ
end Formalism.HermitianLattices.Ext.L3.WittTransvections
