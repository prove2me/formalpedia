-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.D2.smul_mem_locF
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T09:47:58.391668+00:00
-- url     : https://prove2.me/submissions/a13d77ef-2901-4e22-ae23-36692558140a

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ApplyMemSmul
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsMulDvdUnif
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_D2_mem_pK
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_D2_notMem_ne_zero
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_D2_inv_smul_mem

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
theorem _root_.solution {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) (A₀ : Submodule (𝓞 K) V)
    {a : K} {x : V} (ha : a ∈ pK K 𝔭 0) (hx : x ∈ locF 𝔭 A₀) : a • x ∈ locF 𝔭 A₀ := by
  obtain ⟨t, ht, w, -, e'⟩ := (mem_pK h𝔭).1 ha
  have := inv_smul_mem h𝔭 A₀ ht ((locF 𝔭 A₀).smul_mem w hx)
  rw [← algebraMap_smul K w, e', smul_smul, ← mul_assoc, inv_mul_cancel₀ (notMem_ne_zero ht),
    one_mul] at this
  exact this
end Formalism.HermitianLattices.Ext.L3.D2
