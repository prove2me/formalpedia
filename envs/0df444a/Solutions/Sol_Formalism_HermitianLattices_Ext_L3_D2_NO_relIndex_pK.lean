-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.D2.NO.relIndex_pK
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T10:11:43.927643+00:00
-- url     : https://prove2.me/submissions/1c952967-60f9-486e-aaca-350e088e0f8f

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsDualBound
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsMulEqUnifPow
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_D2_NO_exists_sub_mem
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_D2_NO_comap_pK
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_D2_algebraMap_mem_pK
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_D2_pK_anti
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_idealPowerSpanBounds_absNorm_extP_eq_sq


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
open Formalism.HermitianLattices.Ext.L3.D2.NO
namespace Formalism.HermitianLattices.Ext.L3.D2.NO
theorem _root_.solution (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) (k : ℕ) :
    (pK K 𝔭 k).toAddSubgroup.relIndex (pK K 𝔭 0).toAddSubgroup = Ideal.absNorm 𝔭 ^ (2 * k) := by
  have h1 : (algebraMap (𝓞 K) K).toAddMonoidHom.range ⊔ (pK K 𝔭 k).toAddSubgroup =
      (pK K 𝔭 0).toAddSubgroup := by
    apply le_antisymm
    · refine sup_le ?_ (pK_anti 𝔭 (Nat.zero_le k))
      rintro _ ⟨z, rfl⟩
      exact algebraMap_mem_pK 𝔭 z
    · intro a ha
      obtain ⟨z, hz⟩ := exists_sub_mem h𝔭 k ha
      rw [show a = algebraMap (𝓞 K) K z + (a - algebraMap (𝓞 K) K z) by ring]
      exact add_mem (AddSubgroup.mem_sup_left ⟨z, rfl⟩) (AddSubgroup.mem_sup_right hz)
  rw [← h1, AddSubgroup.relIndex_sup_right, ← AddSubgroup.index_comap, comap_pK h𝔭,
    ← Ideal.absNorm_eq_index, map_pow, idealPowerSpanBounds.absNorm_extP_eq_sq hK hF h𝔭, ← pow_mul]
end Formalism.HermitianLattices.Ext.L3.D2.NO
