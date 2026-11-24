-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.LIOrb.IA.mem_locF_of_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T09:48:28.175604+00:00
-- url     : https://prove2.me/submissions/1e975c5c-a836-48b4-84e5-347737efb080

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_AbsNormDiscrIdealOfLe
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_FinrankRingOfIntegers
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_VdEqZeroOfNotLe
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsMulDvdUnif
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CardEqRelIndex
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_LocF_mem_locF_iff


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
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.LIOrb Formalism.HermitianLattices.Ext.L3.LIOrb.IA
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
local notation "ι" => algebraMap (𝓞 F) (𝓞 K)
namespace Formalism.HermitianLattices.Ext.L3.LIOrb.IA
theorem _root_.solution {𝔭 : Ideal (𝓞 F)} (hp : 𝔭.IsPrime) {N : Submodule (𝓞 K) V} {t : 𝓞 F}
    (ht : t ∉ 𝔭) {x : V} (hx : ι t • x ∈ locF 𝔭 N) : x ∈ locF 𝔭 N := by
  obtain ⟨s, hs, h⟩ := (LocF.mem_locF_iff hp N _).1 hx
  refine (LocF.mem_locF_iff hp N x).2 ⟨s * t, fun hm => (hp.mem_or_mem hm).elim hs ht, ?_⟩
  rwa [map_mul, mul_smul]
end Formalism.HermitianLattices.Ext.L3.LIOrb.IA
