-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.finite_repSet_of_ortho
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T10:11:30.659198+00:00
-- url     : https://prove2.me/submissions/f5b123ac-c027-4d01-90bf-e60c657f627b

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_FiniteDimensionalOfOrtho
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_AutFinite
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_FiniteRepSetOfOrtho
import Theorems.Thm_Formalism_HermitianLatticesTheory_autFinite_short
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_trace_pos_of_ortho


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
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
namespace Formalism.HermitianLattices.Ext.L3
theorem _root_.solution (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) {h : V →ₗ⋆[K] V →ₗ[K] K}
    (hs : h.IsSymm) {I : Submodule (𝓞 K) V} {n : ℕ} (hI : Formalism.HermitianLatticesTheory.IsOrthoLattice h I n)
    {L : Submodule (𝓞 K) V} (hL : Submodule.IsLattice K L) (t : K) :
    {x : V | x ∈ L ∧ h x x = t}.Finite := by
  have := hL
  refine (Formalism.HermitianLatticesTheory.autFinite_short h (trace_pos_of_ortho hK hs hI) L
    (Algebra.trace ℚ K t)).subset ?_
  rintro x ⟨hx, rfl⟩
  exact ⟨hx, le_rfl⟩
end Formalism.HermitianLattices.Ext.L3
