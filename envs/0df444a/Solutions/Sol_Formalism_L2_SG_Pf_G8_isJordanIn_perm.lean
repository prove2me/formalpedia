-- Prove2me | solution 1 for Formalism.L2.SG.Pf.G8.isJordanIn_perm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:27:59.173361+00:00
-- url     : https://prove2.me/submissions/61e18b9e-95b1-4e6b-adc5-140f2168e77a

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_FibPNeZeroOfGenus
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_IsomFixOfExp
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_ExistsPermOfMin

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
theorem _root_.solution {h : V →ₗ⋆[K] V →ₗ[K] K} {X : Submodule K V} {L : Submodule (𝓞 K) V}
    {𝔭 : Ideal (𝓞 F)} {b : Fin (finrank K X) → V} {a : Fin (finrank K X) → 𝓞 F}
    (hb : IsJordanIn h X L 𝔭 b a) (σ : Equiv.Perm (Fin (finrank K X))) :
    IsJordanIn h X L 𝔭 (b ∘ σ) (a ∘ σ) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := hb
  have hr : Set.range (b ∘ σ) = Set.range b := σ.surjective.range_comp b
  refine ⟨fun i => h1 _, ?_, fun i j hij => h3 _ _ (σ.injective.ne hij), fun i => h4 _,
    fun i => h5 _⟩
  rw [hr]
  exact h2
end Formalism.L2.SG.Pf.G8
