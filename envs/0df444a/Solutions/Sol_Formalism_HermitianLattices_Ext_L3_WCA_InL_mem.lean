-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.WCA.InL.mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T09:32:41.829798+00:00
-- url     : https://prove2.me/submissions/53b6a450-3a64-4582-a573-90eb5eaa3a7f

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_AkCountEqRedCountMul
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_MemSmulOfMemSmulLocF
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_FinitePrimesOfMem
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_InLZeroIff
import Theorems.Thm_P2M_Formalism_HermitianLattices_Ext_L3_WCA____ne_zero_cf941fa073ca
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_WCA_ne_zero_of_notMem
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_WCA_InI_add
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_WCA_InL_add
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_WCA_InL_smul
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_Ent_add
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_Ent_smul
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_ne_zero_of_notMem
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
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.WCA
open LocalSpans idealPowerSpanBounds localizedQuotients
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
local notation "ι" => algebraMap (𝓞 F) (𝓞 K)
local notation "κ" => algebraMap (𝓞 K) K
variable {𝔭 : Ideal (𝓞 F)} {A : Submodule (𝓞 K) V}
namespace Formalism.HermitianLattices.Ext.L3.WCA
namespace InL
theorem _root_.solution (hp : 𝔭.IsPrime) {k : ℕ} {v : V} (hv : InL 𝔭 A k v) :
    v ∈ extP K 𝔭 ^ k • locF 𝔭 A := by
  obtain ⟨t, ht, e⟩ := hv
  have ht0 := κι_ne_zero (K := K) (ne_zero_of_notMem ht)
  have key : ∀ p ∈ extP K 𝔭 ^ k • A, (κ (ι t))⁻¹ • p ∈ extP K 𝔭 ^ k • locF 𝔭 A := by
    intro p hp'
    induction hp' using Submodule.smul_induction_on' with
    | smul a ha m hm =>
      rw [smul_comm]
      refine Submodule.smul_mem_smul ha ((mem_locF 𝔭 A _).2 ⟨t, ht, ?_⟩)
      rw [← algebraMap_smul K (ι t), smul_smul, mul_inv_cancel₀ ht0, one_smul]
      exact hm
    | add x _ y _ hx hy =>
      rw [smul_add]
      exact add_mem hx hy
  have := key _ e
  rwa [← algebraMap_smul K (ι t), smul_smul, inv_mul_cancel₀ ht0, one_smul] at this
end InL
end Formalism.HermitianLattices.Ext.L3.WCA
