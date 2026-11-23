-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.U0.IsSD.cut
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:25:10.34419+00:00
-- url     : https://prove2.me/submissions/7b3fb06c-d216-4463-b947-d2c79fb1c773

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsPrimitiveNorm
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsIsomScale
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_U0_mem_cutW
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_U0_mem_cutM
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_U0_IsLatIn_cut
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_U0_int_of_cut

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
namespace IsSD
theorem _root_.solution (hM : IsSD S h W M) {X : V} (hX : X ∈ M) (hu : IsUnitIn S (h X X)) :
    IsSD S h (cutW h W X) (cutM h M X) := by
  refine ⟨hM.toIsLatIn.cut X, fun x hx hxS => ?_⟩
  obtain ⟨hxW, hx0⟩ := mem_cutW.1 hx
  exact mem_cutM.2 ⟨hM.dual x hxW (int_of_cut hM.toIsLatIn hX hu hx0 hxS), hx0⟩
end IsSD
end Formalism.HermitianLattices.Ext.L3.U0
