-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.D2.NO.zR_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T09:52:02.500343+00:00
-- url     : https://prove2.me/submissions/1f130b9a-c543-452a-bd69-ca220bf9b724

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsDualBound
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsMulEqUnifPow
import Theorems.Thm_P2M_Formalism_HermitianLattices_Ext_L3_D2_NO_mul_mem__c3251c59e9fe

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
theorem _root_.solution {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {z : K} (hz : z ∈ pK K 𝔭 0) :
    zR 𝔭 z ≤ (pK K 𝔭 0).toAddSubgroup := by
  rintro a ⟨b, hb, rfl⟩
  exact mul_mem₀ h𝔭 hz hb
end Formalism.HermitianLattices.Ext.L3.D2.NO
