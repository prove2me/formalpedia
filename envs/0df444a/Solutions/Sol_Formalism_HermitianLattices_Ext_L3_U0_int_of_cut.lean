-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.U0.int_of_cut
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:16:49.799853+00:00
-- url     : https://prove2.me/submissions/05d42b3e-7032-4908-8e51-914fb85c2ed8

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsPrimitiveNorm
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsIsomScale
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_U0_proj_mem

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
theorem _root_.solution (hM : IsLatIn S h W M) {X : V} (hX : X ∈ M)
    (hu : IsUnitIn S (h X X)) {x : V} (hXx : h X x = 0) (hx : ∀ m ∈ cutM h M X, h m x ∈ S) :
    ∀ m ∈ M, h m x ∈ S := by
  intro m hm
  have hp := hx _ (proj_mem hM hX hu hm)
  rw [LinearMap.map_sub₂, LinearMap.map_smulₛₗ₂, hXx, smul_zero, sub_zero] at hp
  exact hp
end Formalism.HermitianLattices.Ext.L3.U0
