-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.D2.unif_pow_mem_pK
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T09:46:19.481101+00:00
-- url     : https://prove2.me/submissions/368b3820-f3e0-42b7-b817-5c26bbc4ed84

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ApplyMemSmul
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsMulDvdUnif
import Theorems.Thm_P2M_Formalism_HermitianLattices_Ext_L3_D2_algebraMap_mem_pK__28aaf4c3f0e6

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
local notation "ι" => algebraMap (𝓞 F) (𝓞 K)
namespace Formalism.HermitianLattices.Ext.L3.D2
theorem _root_.solution {𝔭 : Ideal (𝓞 F)} {π : 𝓞 F} (hπ : π ∈ 𝔭) (k : ℕ) :
    algebraMap F K (π : F) ^ k ∈ pK K 𝔭 k := by
  have h1 : (ι π) ^ k ∈ extP K 𝔭 ^ k := Ideal.pow_mem_pow (Ideal.mem_map_of_mem _ hπ) k
  have h2 := algebraMap_mem_pK' (K := K) 𝔭 h1
  convert h2 using 1
  rw [map_pow]
  congr 1
end Formalism.HermitianLattices.Ext.L3.D2
