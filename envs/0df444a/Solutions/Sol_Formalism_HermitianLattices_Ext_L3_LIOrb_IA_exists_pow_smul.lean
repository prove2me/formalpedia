-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.LIOrb.IA.exists_pow_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T09:48:18.413797+00:00
-- url     : https://prove2.me/submissions/784a00a9-5442-493c-8a22-418ec54bef27

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_AbsNormDiscrIdealOfLe
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_FinrankRingOfIntegers
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_VdEqZeroOfNotLe
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsMulDvdUnif
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CardEqRelIndex
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_D2_exists_mul_dvd
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_LocF_algebraMap_intCast_smul
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_LocF_exists_zsmul_le
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
theorem _root_.solution {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {M N : Submodule (𝓞 K) V}
    (hM : Submodule.IsLattice K M) (hN : Submodule.IsLattice K N) :
    ∃ r : ℕ, ∀ a ∈ 𝔭 ^ r, ∀ y ∈ M, ι a • y ∈ locF 𝔭 N := by
  have hp := h𝔭.isPrime
  obtain ⟨n, hn, hnx⟩ := LocF.exists_zsmul_le hM hN
  have hn' : (n : 𝓞 F) ≠ 0 := by exact_mod_cast hn
  obtain ⟨r, u, hu, hdvd⟩ := D2.exists_mul_dvd h𝔭 hn'
  refine ⟨r, fun a ha y hy => ?_⟩
  rw [LocF.mem_locF_iff hp]
  refine ⟨u, hu, ?_⟩
  obtain ⟨d, hd⟩ := hdvd a ha
  rw [smul_smul, ← map_mul, hd, map_mul, mul_comm, mul_smul, LocF.algebraMap_intCast_smul]
  exact N.smul_mem _ (hnx y hy)
end Formalism.HermitianLattices.Ext.L3.LIOrb.IA
