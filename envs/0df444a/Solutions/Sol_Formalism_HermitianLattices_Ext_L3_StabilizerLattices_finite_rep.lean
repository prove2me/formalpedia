-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.StabilizerLattices.finite_rep
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:16:08.089432+00:00
-- url     : https://prove2.me/submissions/ce2177d0-3f1e-4599-8ad9-79143923781c

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsSmulMem
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsClassReps
import Theorems.Thm_Formalism_HermitianLatticesTheory_autFinite_short
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_StabilizerLattices_trace_pos


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
open Formalism.HermitianLattices.Ext.L3.StabilizerLattices
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
variable {h : V →ₗ⋆[K] V →ₗ[K] K}
namespace Formalism.HermitianLattices.Ext.L3.StabilizerLattices
theorem _root_.solution (hd : IsTotPosDef h) {M : Submodule (𝓞 K) V} (hM : Submodule.IsLattice K M)
    (n : K) : {x : V | x ∈ M ∧ h x x = n}.Finite := by
  have := hM
  refine (Formalism.HermitianLatticesTheory.autFinite_short h (trace_pos hd) M (Algebra.trace ℚ K n)).subset ?_
  rintro x ⟨hx, rfl⟩
  exact ⟨hx, le_rfl⟩
end Formalism.HermitianLattices.Ext.L3.StabilizerLattices
