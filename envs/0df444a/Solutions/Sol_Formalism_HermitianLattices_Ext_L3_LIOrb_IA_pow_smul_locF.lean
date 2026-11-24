-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.LIOrb.IA.pow_smul_locF
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T09:58:07.869189+00:00
-- url     : https://prove2.me/submissions/76f42384-8395-4c6d-9afb-58bafc67d3b0

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_AbsNormDiscrIdealOfLe
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_FinrankRingOfIntegers
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_VdEqZeroOfNotLe
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsMulDvdUnif
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CardEqRelIndex
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_LIOrb_IA_mem_locF_of_smul
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
theorem _root_.solution {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {M N : Submodule (𝓞 K) V} {r : ℕ}
    (hr : ∀ a ∈ 𝔭 ^ r, ∀ y ∈ M, ι a • y ∈ locF 𝔭 N) {a : 𝓞 F} (ha : a ∈ 𝔭 ^ r) {x : V}
    (hx : x ∈ locF 𝔭 M) : ι a • x ∈ locF 𝔭 N := by
  obtain ⟨t, ht, htx⟩ := (LocF.mem_locF_iff h𝔭.isPrime M x).1 hx
  apply mem_locF_of_smul h𝔭.isPrime ht
  rw [smul_comm]
  exact hr a ha _ htx
end Formalism.HermitianLattices.Ext.L3.LIOrb.IA
