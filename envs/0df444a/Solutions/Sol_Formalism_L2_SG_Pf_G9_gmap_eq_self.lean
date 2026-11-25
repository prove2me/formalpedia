-- Prove2me | solution 1 for Formalism.L2.SG.Pf.G9.gmap_eq_self
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:34:47.981285+00:00
-- url     : https://prove2.me/submissions/378b1dc6-ca49-42eb-8863-24022ddc471b

import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_JordanExists
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsRepsOfCover
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsSmulMem
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_InvMemLocROfUnimod
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_FiniteRepSetOfOrtho
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_IsomAct
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_NondegenerateOnOrthCompl
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_BallB_IsStep_change


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
    (hg : g ∈ isomFix h U) {M : Submodule (𝓞 K) V} (hM : ∀ x ∈ M, x ∈ U) :
    Formalism.HermitianLatticesTheory.gmap g M = M := by
  ext x
  rw [Formalism.HermitianLatticesTheory.gmap, Submodule.mem_map]
  constructor
  · rintro ⟨y, hy, e⟩
    have e2 : g y = y := hg.2 y (hM y hy)
    rw [← e]
    change g y ∈ M
    rw [e2]
    exact hy
  · intro hx
    exact ⟨x, hx, hg.2 x (hM x hx)⟩
end Formalism.L2.SG.Pf.G9
