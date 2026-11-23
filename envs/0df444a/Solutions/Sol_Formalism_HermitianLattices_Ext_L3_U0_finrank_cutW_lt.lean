-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.U0.finrank_cutW_lt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:17:16.219554+00:00
-- url     : https://prove2.me/submissions/75ec8630-d619-43df-99d0-d9ef8a140d59

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsIsomScale
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsOrthTransfer

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
theorem _root_.solution {W : Submodule K V} {x : V} (hx : x ∈ W) (hxx : h x x ≠ 0) :
    finrank K (cutW h W x) < finrank K W := by
  unfold cutW
  apply Submodule.finrank_lt_finrank_of_lt
  refine lt_of_le_of_ne inf_le_left fun heq => hxx ?_
  have hmem : x ∈ W ⊓ LinearMap.ker (h x) := by
    rw [heq]
    exact hx
  exact LinearMap.mem_ker.mp (Submodule.mem_inf.mp hmem).2
end Formalism.HermitianLattices.Ext.L3.U0
