-- Prove2me | solution 1 for Formalism.L2.SG.Pf.G9.gmap_cutU
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:39:43.933908+00:00
-- url     : https://prove2.me/submissions/320c57c8-6783-4f35-9e85-1f0b3e3954ad

import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_JordanExists
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsRepsOfCover
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsSmulMem
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_InvMemLocROfUnimod
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_FiniteRepSetOfOrtho
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_IsomAct
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_NondegenerateOnOrthCompl
import Theorems.Thm_Formalism_L2_SG_Pf_G9_gmap_inf_sub

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
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.G9
open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt
variable {K F V : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F]
  [Algebra F K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]
namespace Formalism.L2.SG.Pf.G9
theorem _root_.solution {h : V →ₗ⋆[K] V →ₗ[K] K} {U : Submodule K V} {g : V ≃ₗ[K] V}
    (hg : g ∈ isomFix h U) (Λ : Submodule (𝓞 K) V) :
    Formalism.HermitianLatticesTheory.gmap g (Λ ⊓ U.restrictScalars (𝓞 K)) =
      Formalism.HermitianLatticesTheory.gmap g Λ ⊓ U.restrictScalars (𝓞 K) := by
  refine gmap_inf_sub _ (fun x hx => by rw [hg.2 x hx]; exact hx) (fun x hx => ?_) Λ
  rw [g.symm_apply_eq.mpr (hg.2 x hx).symm]
  exact hx
end Formalism.L2.SG.Pf.G9
