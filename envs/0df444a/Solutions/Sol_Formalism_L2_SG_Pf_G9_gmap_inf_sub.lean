-- Prove2me | solution 1 for Formalism.L2.SG.Pf.G9.gmap_inf_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:27:57.209583+00:00
-- url     : https://prove2.me/submissions/df6bbada-05a3-4716-8e47-d8e589412577

import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_JordanExists
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsRepsOfCover
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsSmulMem
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_InvMemLocROfUnimod
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_FiniteRepSetOfOrtho
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_IsomAct
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_NondegenerateOnOrthCompl

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
theorem _root_.solution {g : V ≃ₗ[K] V} (X : Submodule K V) (h1 : ∀ x ∈ X, g x ∈ X)
    (h2 : ∀ x ∈ X, g.symm x ∈ X) (Λ : Submodule (𝓞 K) V) :
    Formalism.HermitianLatticesTheory.gmap g (Λ ⊓ X.restrictScalars (𝓞 K)) =
      Formalism.HermitianLatticesTheory.gmap g Λ ⊓ X.restrictScalars (𝓞 K) := by
  have hinj : Function.Injective ((g : V →ₗ[K] V).restrictScalars (𝓞 K)) :=
    fun a b e => g.injective e
  rw [Formalism.HermitianLatticesTheory.gmap, Submodule.map_inf _ hinj]
  congr 1
  ext x
  rw [Submodule.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact h1 y hy
  · intro hx
    exact ⟨g.symm x, h2 x hx, g.apply_symm_apply x⟩
end Formalism.L2.SG.Pf.G9
