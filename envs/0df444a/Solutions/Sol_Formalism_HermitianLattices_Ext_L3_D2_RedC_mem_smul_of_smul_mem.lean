-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.D2.RedC.mem_smul_of_smul_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T10:36:41.505391+00:00
-- url     : https://prove2.me/submissions/9509ec1f-9a28-496d-8e80-093aff0ae470

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsDualBound
import Definitions.Def_Lemmata_GeneralBFactLeftRest_Imports
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_MemLocFOfSmulMem
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_D2_smul_mem_smul
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_MeanA_exists_mul_sub_one_mem_pow


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
theorem _root_.solution {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) (A : Submodule (𝓞 K) V) (k : ℕ)
    {t : 𝓞 F} (ht : t ∉ 𝔭) {v : V} (hv : v ∈ A)
    (h : algebraMap (𝓞 F) (𝓞 K) t • v ∈ extP K 𝔭 ^ k • A) : v ∈ extP K 𝔭 ^ k • A := by
  obtain ⟨u, hu⟩ := MeanA.exists_mul_sub_one_mem_pow h𝔭 ht k
  have : v = algebraMap (𝓞 F) (𝓞 K) u • (algebraMap (𝓞 F) (𝓞 K) t • v) -
      algebraMap (𝓞 F) (𝓞 K) (u * t - 1) • v := by
    rw [map_sub, map_mul, map_one, sub_smul, mul_smul, one_smul]; abel
  rw [this]
  exact sub_mem (Submodule.smul_mem _ _ h) (Submodule.smul_mem_smul (localizedQuotients.ι_mem_pow hu) hv)
end Formalism.HermitianLattices.Ext.L3.D2.RedC
