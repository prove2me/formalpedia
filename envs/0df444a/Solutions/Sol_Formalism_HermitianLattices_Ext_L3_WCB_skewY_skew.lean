-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.WCB.skewY_skew
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T09:49:17.050639+00:00
-- url     : https://prove2.me/submissions/a1944a41-702c-4240-9323-e26733e17781

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_InLZeroIff
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_LaurentAdjoinEqOfImageEq
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_WCB_skewY_apply
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
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.WCB
variable {K : Type} [Field K] [StarRing K] {V : Type} [AddCommGroup V] [Module K V]
namespace Formalism.HermitianLattices.Ext.L3.WCB
theorem _root_.solution {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (u w : V) {θ : K} (hθ : star θ = -θ)
    (a b : V) : h (skewY h u w θ a) b + h a (skewY h u w θ b) = 0 := by
  have e1 : star (h u a) = h a u := hs.eq u a
  have e2 : star (h w a) = h a w := hs.eq w a
  rw [skewY_apply, skewY_apply]
  simp only [map_add, map_smul, map_smulₛₗ, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
    starRingEnd_apply, star_sub, star_mul', e1, e2, hθ]
  ring
end Formalism.HermitianLattices.Ext.L3.WCB
