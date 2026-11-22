-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.U0.IsLatIn.cut
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:45:20.198813+00:00
-- url     : https://prove2.me/submissions/7b462a2e-78cc-4824-9206-bf5fd9d377a6

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsPrimitiveNorm
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsIsomScale
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_U0_mem_cutW
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_U0_mem_cutM

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
namespace IsLatIn
theorem _root_.solution (hM : IsLatIn S h W M) (X : V) : IsLatIn S h (cutW h W X) (cutM h M X) where
  le := fun m hm => mem_cutW.mpr ⟨hM.le m (mem_cutM.mp hm).1, (mem_cutM.mp hm).2⟩
  smul_mem := fun a ha m hm => mem_cutM.mpr ⟨hM.smul_mem a ha m (mem_cutM.mp hm).1, by
    rw [map_smul, (mem_cutM.mp hm).2, smul_zero]⟩
  int := fun x hx y hy => hM.int x (mem_cutM.mp hx).1 y (mem_cutM.mp hy).1
  span := fun x hx => by
    obtain ⟨t, ht0, ht⟩ := hM.span x (mem_cutW.mp hx).1
    exact ⟨t, ht0, mem_cutM.mpr ⟨ht, by rw [map_smul, (mem_cutW.mp hx).2, smul_zero]⟩⟩
end IsLatIn
end Formalism.HermitianLattices.Ext.L3.U0
