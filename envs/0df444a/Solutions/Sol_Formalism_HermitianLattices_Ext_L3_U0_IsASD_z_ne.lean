-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.U0.IsASD.z_ne
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:38:23.158827+00:00
-- url     : https://prove2.me/submissions/253afb67-5ba7-4bce-9f97-5857e8946249

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsIsomScale
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsOrthTransfer
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_U0_IsASD_z_norm_ne


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
open WA Module
variable {K V : Type*} [Field K] [StarRing K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]
variable {S : Subring K} {π : K} {h : V →ₗ⋆[K] V →ₗ[K] K}
namespace Formalism.HermitianLattices.Ext.L3.U0
namespace IsASD
theorem _root_.solution {W : Submodule K V} {M : AddSubgroup V} {z : V} (hM : IsASD S π h W M z) :
    z ≠ 0 := by
  intro hz
  exact hM.z_norm_ne (by simp [hz])
end IsASD
end Formalism.HermitianLattices.Ext.L3.U0
