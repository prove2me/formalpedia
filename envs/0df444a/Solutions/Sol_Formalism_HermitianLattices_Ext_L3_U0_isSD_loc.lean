-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.U0.isSD_loc
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:15:49.469706+00:00
-- url     : https://prove2.me/submissions/bb4cdf7a-9c8a-4556-94a5-8ef84a5e75f1

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_IsUnimodularAtIffVd
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsOrthTransfer
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsIsASDOfTuple
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsFracOfFixed
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsIsomLocFOfVdZero
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_WA_isSelfDualMod_loc


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
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]
open Formalism.HermitianLattices.Ext.L3.U0
open WA
omit [FiniteDimensional K V]
namespace Formalism.HermitianLattices.Ext.L3.U0
theorem _root_.solution {h : V →ₗ⋆[K] V →ₗ[K] K} {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsLattice K L) {P : Ideal (𝓞 K)} (hP : P.IsPrime)
    (hu : Formalism.HermitianLatticesTheory.IsUnimodularAt h P L) :
    IsSD (locRing P) h ⊤ (Formalism.HermitianLatticesTheory.loc (K := K) P L).toAddSubgroup := by
  have h0 := isSelfDualMod_loc hL hP hu
  exact ⟨⟨fun _ _ => Submodule.mem_top, h0.smul_mem, h0.int, fun x _ => h0.span x⟩,
    fun x _ hx => h0.dual x hx⟩
end Formalism.HermitianLattices.Ext.L3.U0
