-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.U0.symm_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:41:15.423329+00:00
-- url     : https://prove2.me/submissions/4733d458-8fff-4d80-8672-9f75ca2bed70

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsPrimitiveNorm
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsIsomScale
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
variable {K V : Type*} [Field K] [StarRing K] [AddCommGroup V] [Module K V]
variable {S : Subring K} {π : K} {h : V →ₗ⋆[K] V →ₗ[K] K} {W : Submodule K V} {M : AddSubgroup V}
namespace Formalism.HermitianLattices.Ext.L3.U0
theorem _root_.solution (hs : h.IsSymm) {x y : V} (hxy : h x y = 0) : h y x = 0 := by
  have e := hs.eq x y
  rw [hxy, map_zero] at e
  exact e.symm
end Formalism.HermitianLattices.Ext.L3.U0
