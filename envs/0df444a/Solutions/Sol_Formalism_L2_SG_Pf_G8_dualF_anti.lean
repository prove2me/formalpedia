-- Prove2me | solution 1 for Formalism.L2.SG.Pf.G8.dualF_anti
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:55:04.169929+00:00
-- url     : https://prove2.me/submissions/f693870c-58b9-447e-820c-601556947ec4

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_JordanExists
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_LocFSubspace
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_IsUnimodularAtIffVd
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ApplyMemSmulOfMemAutSub
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_IsLatticeOfFibReps
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_ExistsLocFEq
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
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.G8
open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt
variable {K F V : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F]
  [Algebra F K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]
namespace Formalism.L2.SG.Pf.G8
theorem _root_.solution (h : V →ₗ⋆[K] V →ₗ[K] K) (𝔭 : Ideal (𝓞 F)) {A B : Submodule (𝓞 K) V} (hAB : A ≤ B) :
    dualF h 𝔭 B ≤ dualF h 𝔭 A := by
  intro x hx
  have hx' : ∀ y ∈ B, h y x ∈ locF 𝔭 (1 : Submodule (𝓞 K) K) := hx
  change ∀ y ∈ A, h y x ∈ locF 𝔭 (1 : Submodule (𝓞 K) K)
  exact fun y hy => hx' y (hAB hy)
end Formalism.L2.SG.Pf.G8
