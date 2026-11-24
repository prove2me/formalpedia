-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.D2.coe_mem_of_mem_smul_top
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T09:48:18.424118+00:00
-- url     : https://prove2.me/submissions/8969f4b9-47a9-4c0d-88d1-177016a0e778

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsDualBound
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CoeMemOfMemSmulTop

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
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.D2
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]
namespace Formalism.HermitianLattices.Ext.L3.D2
theorem _root_.solution (I : Ideal (𝓞 K)) (A : Submodule (𝓞 K) V) {u : ↥A}
    (hu : u ∈ (I • ⊤ : Submodule (𝓞 K) ↥A)) : (u : V) ∈ I • A := by
  have h2 := Submodule.mem_map_of_mem (f := A.subtype) hu
  rwa [Submodule.map_smul'', Submodule.map_subtype_top] at h2
end Formalism.HermitianLattices.Ext.L3.D2
