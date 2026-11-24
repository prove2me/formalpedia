-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.D2.nO_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T10:02:21.064065+00:00
-- url     : https://prove2.me/submissions/7f3a73f1-aafb-48e1-aeab-8063134e1ad3

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsDualBound
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsMulEqUnifPow
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_D2_NO_zR_le
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_D2_NO_zR_mul

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
open NO
namespace Formalism.HermitianLattices.Ext.L3.D2
theorem _root_.solution {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {z w : K} (hz : z ∈ pK K 𝔭 0) (hz0 : z ≠ 0)
    (hw : w ∈ pK K 𝔭 0) : nO 𝔭 (z * w) = nO 𝔭 z * nO 𝔭 w := by
  have h1 := AddSubgroup.relIndex_mul_relIndex ((zR 𝔭 w).map (AddMonoidHom.mulLeft z)) (zR 𝔭 z)
    (pK K 𝔭 0).toAddSubgroup (AddSubgroup.map_mono (zR_le h𝔭 hw)) (zR_le h𝔭 hz)
  have h2 : ((zR 𝔭 w).map (AddMonoidHom.mulLeft z)).relIndex (zR 𝔭 z) = nO 𝔭 w :=
    AddSubgroup.relIndex_map_map_of_injective _ _ (mul_right_injective₀ hz0)
  rw [h2, ← zR_mul] at h1
  rw [mul_comm (nO 𝔭 z)]
  exact h1.symm
end Formalism.HermitianLattices.Ext.L3.D2
