-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.D2.smul_mem_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T10:23:08.312659+00:00
-- url     : https://prove2.me/submissions/f99d4b54-5e87-4299-a4e5-909e5a12a847

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ApplyMemSmul
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsMulDvdUnif
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_D2_exists_unif
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_D2_mem_pK_iff_unif
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_D2_mem_smul_iff_unif
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_D2_smul_mem_locF

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
theorem _root_.solution {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) (A₀ : Submodule (𝓞 K) V) {i j : ℕ}
    {a : K} {x : V} (ha : a ∈ pK K 𝔭 i) (hx : x ∈ extP K 𝔭 ^ j • locF 𝔭 A₀) :
    a • x ∈ extP K 𝔭 ^ (i + j) • locF 𝔭 A₀ := by
  obtain ⟨π, hπ, hπ'⟩ := exists_unif h𝔭
  obtain ⟨b, hb, rfl⟩ := (mem_pK_iff_unif h𝔭 hπ hπ').1 ha
  obtain ⟨y, hy, rfl⟩ := (mem_smul_iff_unif h𝔭 hπ hπ' A₀).1 hx
  refine (mem_smul_iff_unif h𝔭 hπ hπ' A₀).2 ⟨b • y, smul_mem_locF h𝔭 A₀ hb hy, ?_⟩
  rw [smul_smul, smul_smul, pow_add]
  congr 1; ring
end Formalism.HermitianLattices.Ext.L3.D2
