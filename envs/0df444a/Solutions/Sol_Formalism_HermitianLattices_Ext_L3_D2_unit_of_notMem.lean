-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.D2.unit_of_notMem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T10:00:49.896775+00:00
-- url     : https://prove2.me/submissions/29447364-dcc6-4e5b-9856-b7146d267df2

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsMulEqUnifPow
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_MulMemPrimePower
import Theorems.Thm_P2M_Formalism_HermitianLattices_Ext_L3_D2_c__ne_zero_3faafbcab9f8
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_D2_mem_pK_zero_of_mul
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_D2_algebraMap_mem_pK


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
theorem _root_.solution {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {s : 𝓞 F} (hs𝔭 : s ∉ 𝔭) :
    algebraMap (𝓞 K) K (ι s) ∈ pK K 𝔭 0 ∧ (algebraMap (𝓞 K) K (ι s))⁻¹ ∈ pK K 𝔭 0 ∧
      algebraMap (𝓞 K) K (ι s) ≠ 0 := by
  have hs0 : s ≠ 0 := fun h0 => hs𝔭 (h0 ▸ zero_mem _)
  have h0 := cι_ne_zero (K := K) hs0
  refine ⟨algebraMap_mem_pK 𝔭 (ι s), ?_, h0⟩
  refine mem_pK_zero_of_mul h𝔭 hs𝔭 (z := 1) ?_
  rw [map_one, mul_inv_cancel₀ h0]
end Formalism.HermitianLattices.Ext.L3.D2
