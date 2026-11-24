-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.D2.nO_unit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T10:02:21.829589+00:00
-- url     : https://prove2.me/submissions/982c388f-256d-4772-bf84-8be92fed3bf5

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsDualBound
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsMulEqUnifPow
import Theorems.Thm_P2M_Formalism_HermitianLattices_Ext_L3_D2_NO_mul_mem__c3251c59e9fe
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_D2_NO_zR_le

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
theorem _root_.solution {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {z : K} (hz : z ∈ pK K 𝔭 0)
    (hz' : z⁻¹ ∈ pK K 𝔭 0) (hz0 : z ≠ 0) : nO 𝔭 z = 1 := by
  have h1 : zR 𝔭 z = (pK K 𝔭 0).toAddSubgroup := by
    apply le_antisymm (zR_le h𝔭 hz)
    intro a ha
    exact ⟨z⁻¹ * a, mul_mem₀ h𝔭 hz' ha, mul_inv_cancel_left₀ hz0 a⟩
  show (zR 𝔭 z).relIndex _ = 1
  rw [h1, AddSubgroup.relIndex_self]
end Formalism.HermitianLattices.Ext.L3.D2
