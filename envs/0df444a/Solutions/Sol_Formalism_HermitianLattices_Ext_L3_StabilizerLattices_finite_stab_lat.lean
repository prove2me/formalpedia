-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.StabilizerLattices.finite_stab_lat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T03:41:50.652821+00:00
-- url     : https://prove2.me/submissions/d07e72c7-0417-4ab3-866e-f86aab4ae113

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsSmulMem
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsClassReps
import Theorems.Thm_Formalism_HermitianLatticesTheory_autFinite
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
theorem _root_.solution (hs : h.IsSymm) (hd : IsTotPosDef h) {M : Submodule (𝓞 K) V}
    (hM : Submodule.IsLattice K M) :
    (MulAction.stabilizer (Formalism.HermitianLatticesTheory.isom h) M : Set (Formalism.HermitianLatticesTheory.isom h)).Finite := by
  have : Finite (Formalism.ThetaLiftIndependence.autL h M) := (Formalism.HermitianLatticesTheory.autFinite K V h hs (trace_pos hd) M hM).to_subtype
  have : Finite (MulAction.stabilizer (Formalism.HermitianLatticesTheory.isom h) M) := Finite.of_equiv _ (stabLatEquiv M).symm
  exact Set.toFinite _
end Formalism.HermitianLattices.Ext.L3.StabilizerLattices
