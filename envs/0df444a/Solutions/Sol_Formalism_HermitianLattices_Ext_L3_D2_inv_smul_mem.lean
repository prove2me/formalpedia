-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.D2.inv_smul_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T09:41:12.179732+00:00
-- url     : https://prove2.me/submissions/601f5dba-6b99-4abe-b427-003d2879a053

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ApplyMemSmul
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsMulDvdUnif
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_D2_notMem_ne_zero
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_LocF_locF_idem
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_LocalSpans_mem_locF
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_MeanB_algebraMap_comp


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
theorem _root_.solution {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) (A₀ : Submodule (𝓞 K) V) {t : 𝓞 F}
    (ht : t ∉ 𝔭) {y : V} (hy : y ∈ locF 𝔭 A₀) : (algebraMap F K (t : F))⁻¹ • y ∈ locF 𝔭 A₀ := by
  have := h𝔭.isPrime
  rw [← LocF.locF_idem 𝔭 A₀]
  refine (LocalSpans.mem_locF 𝔭 _ _).2 ⟨t, ht, ?_⟩
  rw [← algebraMap_smul K (ι t), MeanB.algebraMap_comp, smul_smul,
    mul_inv_cancel₀ (notMem_ne_zero ht), one_smul]
  exact hy
end Formalism.HermitianLattices.Ext.L3.D2
