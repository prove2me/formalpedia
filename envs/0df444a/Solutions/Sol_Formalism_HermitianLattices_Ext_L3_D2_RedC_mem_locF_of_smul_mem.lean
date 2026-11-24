-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.D2.RedC.mem_locF_of_smul_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T09:48:34.790199+00:00
-- url     : https://prove2.me/submissions/8ae19356-6716-464a-ad7d-ac77bf81f87c

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsDualBound
import Definitions.Def_Lemmata_GeneralBFactLeftRest_Imports
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_MemLocFOfSmulMem
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_LocalSpans_mem_locF


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
open Formalism.HermitianLattices.Ext.L3.D2.RedC
namespace Formalism.HermitianLattices.Ext.L3.D2.RedC
theorem _root_.solution {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) (A₀ : Submodule (𝓞 K) V)
    {t : 𝓞 F} (ht : t ∉ 𝔭) {v : V} (h : algebraMap (𝓞 F) (𝓞 K) t • v ∈ locF 𝔭 A₀) : v ∈ locF 𝔭 A₀ := by
  have := h𝔭.isPrime
  obtain ⟨s, hs, h1⟩ := (LocalSpans.mem_locF 𝔭 A₀ _).1 h
  refine (LocalSpans.mem_locF 𝔭 A₀ _).2 ⟨s * t, fun h => (h𝔭.isPrime.mem_or_mem h).elim hs ht, ?_⟩
  rwa [map_mul, mul_smul]
end Formalism.HermitianLattices.Ext.L3.D2.RedC
