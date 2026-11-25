-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.LIOrb.mem_tube_bot
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T07:23:59.536728+00:00
-- url     : https://prove2.me/submissions/c1e34617-0217-49f0-a939-6e916f1073cf

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ApplyMemSmulOfMemAutSub
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CardQuotInfNeZero
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsIsomCongr
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsLatticeVdLeOne
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_IsIntegralAtLocF
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_MemSmulTopIff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module Filter
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.LIOrb
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]
namespace Formalism.HermitianLattices.Ext.L3.LIOrb
theorem _root_.solution {A : Submodule (𝓞 K) V} {𝔭 : Ideal (𝓞 F)} {J : ℕ} {x y : V} :
    y ∈ tube ⊥ A 𝔭 J x ↔ y - x ∈ ((extP K 𝔭) ^ J • A : Submodule (𝓞 K) V) := by
  constructor
  · rintro ⟨g, hg, hy⟩
    rw [Subgroup.mem_bot] at hg
    rwa [hg, DA.one_app] at hy
  · intro hy
    exact ⟨1, one_mem _, by rwa [DA.one_app]⟩
end Formalism.HermitianLattices.Ext.L3.LIOrb
