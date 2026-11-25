-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.LIOrb.DA.mem_smul_top_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T08:04:46.427988+00:00
-- url     : https://prove2.me/submissions/ff647fb1-2b28-489e-82a2-ccdb6cc4a90f

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
open Formalism.HermitianLattices.Ext.L3.LIOrb.DA
namespace Formalism.HermitianLattices.Ext.L3.LIOrb.DA
theorem _root_.solution (A : Submodule (𝓞 K) V) (I : Ideal (𝓞 K)) (w : ↥A) :
    w ∈ (I • ⊤ : Submodule (𝓞 K) ↥A) ↔ (w : V) ∈ (I • A : Submodule (𝓞 K) V) := by
  have e : (I • ⊤ : Submodule (𝓞 K) ↥A).map A.subtype = I • A := by
    rw [Submodule.map_smul'', Submodule.map_top, Submodule.range_subtype]
  rw [← e]
  constructor
  · intro hw
    exact Submodule.mem_map_of_mem hw
  · rintro ⟨w', hw', e'⟩
    rwa [← Subtype.ext (a1 := w') (a2 := w) e']
end Formalism.HermitianLattices.Ext.L3.LIOrb.DA
