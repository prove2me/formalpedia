-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.WittTransvections.transvEquiv_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:17:21.935255+00:00
-- url     : https://prove2.me/submissions/3f9d544e-bf1c-405d-8091-1e3883218d05

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_FiniteDimensionalOfOrtho
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsIsomMapOfEq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3
open Formalism.HermitianLattices.Ext.L3.WittTransvections
variable {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V]
namespace Formalism.HermitianLattices.Ext.L3.WittTransvections
theorem _root_.solution (h : V →ₗ⋆[K] V →ₗ[K] K) (u : V) {ξ : K}
    (hξ : ξ + star ξ = ξ * star ξ * h u u) (v : V) :
    transvEquiv h u hξ v = v - (ξ * h u v) • u := transv_apply h u ξ v
end Formalism.HermitianLattices.Ext.L3.WittTransvections
