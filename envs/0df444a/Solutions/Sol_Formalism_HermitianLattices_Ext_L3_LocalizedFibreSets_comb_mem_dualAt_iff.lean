-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.LocalizedFibreSets.comb_mem_dualAt_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:15:28.083813+00:00
-- url     : https://prove2.me/submissions/95878f05-232d-4978-b4ea-b5d475697c39

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_SumOrbitsEquivariant
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_IsUnimodularAtIffVd
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsIsomLocFOfVdZero
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExtOfSymmApply
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_UnimodularOfMemGenusOrtho
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_InvMemLocROfUnimod
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_SplitA_mul_mem_locR
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_SplitA_one_mem_locR
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_SplitA_star_mem_locR
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_SplitBAux_h_decomp
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_VecSplit_comb_mem_loc_adjoin_iff
import Theorems.Thm_P2M_Formalism_HermitianLattices_Ext_L3_SplitA_mem_dualAt_iff__473848215253


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
theorem _root_.solution (hs : h.IsSymm) (S : VecSplit h h') (p : Ideal (𝓞 K))
    (L' : Submodule (𝓞 K) V') (c : K) (a : V') :
    c • S.x₀ + S.ι a ∈ Formalism.HermitianLatticesTheory.dualAt h p (Formalism.HermitianLatticesTheory.loc (K := K) p (S.adjoin L')) ↔
      c * h S.x₀ S.x₀ ∈ Formalism.HermitianLatticesTheory.locR (K := K) p ∧
        a ∈ Formalism.HermitianLatticesTheory.dualAt h' p (Formalism.HermitianLatticesTheory.loc (K := K) p L') := by
  rw [mem_dualAt_iff', mem_dualAt_iff']
  constructor
  · intro H
    refine ⟨?_, fun b hb => ?_⟩
    · have := H ((1 : K) • S.x₀ + S.ι 0)
        ((S.comb_mem_loc_adjoin_iff p L' 1 0).mpr ⟨one_mem_locR p, Submodule.zero_mem _⟩)
      rwa [SplitBAux.h_decomp hs S, star_one, one_mul, map_zero, LinearMap.zero_apply, add_zero] at this
    · have := H ((0 : K) • S.x₀ + S.ι b)
        ((S.comb_mem_loc_adjoin_iff p L' 0 b).mpr ⟨Submodule.zero_mem _, hb⟩)
      rwa [SplitBAux.h_decomp hs S, star_zero, zero_mul, zero_mul, zero_add] at this
  · rintro ⟨hc, ha⟩ y hy
    obtain ⟨d, b, rfl⟩ := S.cover y
    obtain ⟨hd, hb⟩ := (S.comb_mem_loc_adjoin_iff p L' d b).mp hy
    rw [SplitBAux.h_decomp hs S, mul_assoc]
    exact Submodule.add_mem _ (mul_mem_locR p (star_mem_locR p hd) hc) (ha b hb)
end Formalism.HermitianLattices.Ext.L3.LocalizedFibreSets
