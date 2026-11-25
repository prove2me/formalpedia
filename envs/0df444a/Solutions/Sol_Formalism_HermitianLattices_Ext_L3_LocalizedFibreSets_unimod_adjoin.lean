-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.LocalizedFibreSets.unimod_adjoin
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T05:57:14.542818+00:00
-- url     : https://prove2.me/submissions/786fc896-2904-4160-b0ea-8a1bd2698dda

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_SumOrbitsEquivariant
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_IsUnimodularAtIffVd
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsIsomLocFOfVdZero
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExtOfSymmApply
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_UnimodularOfMemGenusOrtho
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_InvMemLocROfUnimod
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_LocalizedFibreSets_comb_mem_dualAt_iff
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_SplitA_mul_mem_locR
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_VecSplit_comb_mem_dualAt_iff
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_VecSplit_comb_mem_loc_adjoin_iff


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
theorem _root_.solution (hs : h.IsSymm) (S : VecSplit h h') {p : Ideal (𝓞 K)}
    {L' : Submodule (𝓞 K) V'} (hn : h S.x₀ S.x₀ ∈ Formalism.HermitianLatticesTheory.locR (K := K) p)
    (hn' : (h S.x₀ S.x₀)⁻¹ ∈ Formalism.HermitianLatticesTheory.locR (K := K) p)
    (hU : Formalism.HermitianLatticesTheory.IsUnimodularAt h' p L') : Formalism.HermitianLatticesTheory.IsUnimodularAt h p (S.adjoin L') := by
  unfold Formalism.HermitianLatticesTheory.IsUnimodularAt at hU ⊢
  ext v
  obtain ⟨c, a, rfl⟩ := S.cover v
  rw [comb_mem_dualAt_iff hs, S.comb_mem_loc_adjoin_iff, hU]
  refine and_congr_left fun _ => ⟨fun hc => ?_, fun hc => mul_mem_locR p hc hn⟩
  have := mul_mem_locR p hc hn'
  rwa [mul_assoc, mul_inv_cancel₀ S.hx₀, mul_one] at this
end Formalism.HermitianLattices.Ext.L3.LocalizedFibreSets
