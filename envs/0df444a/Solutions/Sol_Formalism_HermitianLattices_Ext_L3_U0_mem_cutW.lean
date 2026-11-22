-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.U0.mem_cutW
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:39:11.89192+00:00
-- url     : https://prove2.me/submissions/aefec1af-d103-4a62-9029-cde6be85e3e3

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsPrimitiveNorm
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsIsomScale

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
theorem _root_.solution {X v : V} : v ∈ cutW h W X ↔ v ∈ W ∧ h X v = 0 := by
  simp [cutW]
end Formalism.HermitianLattices.Ext.L3.U0
