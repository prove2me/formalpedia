-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.LocalizedFibreSets.isIntegralLat_adjoin
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T05:57:08.602542+00:00
-- url     : https://prove2.me/submissions/ef2a6dab-f9be-4954-b100-bf1899df9bf1

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_SumOrbitsEquivariant
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_IsUnimodularAtIffVd
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsIsomLocFOfVdZero
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExtOfSymmApply
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_UnimodularOfMemGenusOrtho
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_InvMemLocROfUnimod
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_SplitBAux_h_decomp
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_SplitBAux_mem_adjoin_iff
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_VecSplit_mem_adjoin_iff


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module Formalism.HermitianLattices.Ext.L3.SplitA
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.LocalizedFibreSets
variable {K F V V' : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F]
  [Algebra F K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V] [AddCommGroup V'] [Module K V'] [FiniteDimensional K V']
  [Module (𝓞 K) V'] [IsScalarTower (𝓞 K) K V']
variable {h : V →ₗ⋆[K] V →ₗ[K] K} {h' : V' →ₗ⋆[K] V' →ₗ[K] K}
namespace Formalism.HermitianLattices.Ext.L3.LocalizedFibreSets
theorem _root_.solution (hs : h.IsSymm) (S : VecSplit h h')
    (hn : h S.x₀ S.x₀ ∈ (1 : Submodule (𝓞 K) K)) {L' : Submodule (𝓞 K) V'}
    (hL' : Formalism.HermitianLatticesTheory.IsIntegralLat h' L') : Formalism.HermitianLatticesTheory.IsIntegralLat h (S.adjoin L') := by
  intro x hx y hy
  obtain ⟨r, a, ha, rfl⟩ := (S.mem_adjoin_iff L' x).mp hx
  obtain ⟨t, b, hb, rfl⟩ := (S.mem_adjoin_iff L' y).mp hy
  obtain ⟨n, hn⟩ := Submodule.mem_one.mp hn
  obtain ⟨w, hw⟩ := Submodule.mem_one.mp (hL' a ha b hb)
  rw [SplitBAux.h_decomp hs S, ← hn, ← hw]
  refine Submodule.mem_one.mpr ⟨conjO K r * t * n + w, ?_⟩
  rw [map_add, map_mul, map_mul]
  rfl
end Formalism.HermitianLattices.Ext.L3.LocalizedFibreSets
