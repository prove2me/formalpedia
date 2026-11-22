-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.U0.proj_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:45:28.458502+00:00
-- url     : https://prove2.me/submissions/6fb75b2c-b658-4b56-9c09-9825a14140c1

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsPrimitiveNorm
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsIsomScale
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
theorem _root_.solution (hM : IsLatIn S h W M) {X : V} (hX : X ∈ M) (hu : IsUnitIn S (h X X)) {m : V}
    (hm : m ∈ M) : m - (h X m * (h X X)⁻¹) • X ∈ cutM h M X := by
  have hc : h X m * (h X X)⁻¹ ∈ S := S.mul_mem (hM.int X hX m hm) hu.2.2
  rw [mem_cutM]
  refine ⟨M.sub_mem hm (hM.smul_mem _ hc _ hX), ?_⟩
  rw [map_sub, map_smul, smul_eq_mul, mul_assoc, inv_mul_cancel₀ hu.1, mul_one, sub_self]
end Formalism.HermitianLattices.Ext.L3.U0
