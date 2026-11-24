-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.WCB.skewY_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T09:30:18.28155+00:00
-- url     : https://prove2.me/submissions/296a46d4-a366-4a9e-b09a-aa6665ce7db2

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_InLZeroIff
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_LaurentAdjoinEqOfImageEq
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
theorem _root_.solution (h : V →ₗ⋆[K] V →ₗ[K] K) (u w : V) (θ : K) (z : V) :
    skewY h u w θ z = (θ * h u z - h w z) • u + h u z • w := by
  simp [skewY]
end Formalism.HermitianLattices.Ext.L3.WCB
