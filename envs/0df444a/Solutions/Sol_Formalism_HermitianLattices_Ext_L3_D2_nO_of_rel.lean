-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.D2.nO_of_rel
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T10:30:40.741914+00:00
-- url     : https://prove2.me/submissions/10f47ed1-eea2-4c0c-90d1-51c947a2c066

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsMulEqUnifPow
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_MulMemPrimePower
import Theorems.Thm_P2M_Formalism_HermitianLattices_Ext_L3_D2_coe___fedd4e958df8
import Theorems.Thm_P2M_Formalism_HermitianLattices_Ext_L3_D2_c__ne_zero_3faafbcab9f8
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_D2_unit_of_notMem
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_D2_exists_unit_factor
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_D2_mul_mem_prime_power
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_D2_algebraMap_mem_pK
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_D2_exists_unif
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_D2_nO_mul
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_D2_nO_unif_pow
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_D2_nO_unit


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
theorem _root_.solution (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal)
    {D s : 𝓞 F} (hD0 : D ≠ 0) (hs𝔭 : s ∉ 𝔭) {G : K}
    (hrel : algebraMap (𝓞 K) K (ι D) = algebraMap (𝓞 K) K (ι s) * G) :
    G ∈ pK K 𝔭 0 ∧ G ≠ 0 ∧ nO 𝔭 G = Ideal.absNorm 𝔭 ^ (2 * vF 𝔭 D) := by
  obtain ⟨π, hπ, hπ'⟩ := exists_unif h𝔭
  have hπ0 : π ≠ 0 := fun h0 => hπ' (h0 ▸ zero_mem _)
  obtain ⟨w, hw, hwi, hw0, ew⟩ := exists_unit_factor (K := K) h𝔭 hπ hπ' hD0
  obtain ⟨hsm, hsi, hsK0⟩ := unit_of_notMem (K := K) h𝔭 hs𝔭
  have hP0 : algebraMap (𝓞 K) K (ι π) ^ vF 𝔭 D ≠ 0 := pow_ne_zero _ (cι_ne_zero hπ0)
  have hPm : algebraMap (𝓞 K) K (ι π) ^ vF 𝔭 D ∈ pK K 𝔭 0 := by
    rw [← map_pow]
    exact algebraMap_mem_pK 𝔭 _
  obtain ⟨u, hu⟩ : ∃ u, u = (algebraMap (𝓞 K) K (ι s))⁻¹ * w := ⟨_, rfl⟩
  have hum : u ∈ pK K 𝔭 0 := by
    rw [hu]
    exact mul_mem_prime_power h𝔭 hsi hw
  have hu0 : u ≠ 0 := by
    rw [hu]
    exact mul_ne_zero (inv_ne_zero hsK0) hw0
  have hui : u⁻¹ ∈ pK K 𝔭 0 := by
    rw [hu, mul_inv, inv_inv]
    exact mul_mem_prime_power h𝔭 hsm hwi
  have hGu : G = algebraMap (𝓞 K) K (ι π) ^ vF 𝔭 D * u := by
    rw [hu]
    rw [ew] at hrel
    apply mul_left_cancel₀ hsK0
    rw [← hrel, mul_left_comm, ← mul_assoc (algebraMap (𝓞 K) K (ι s)), mul_inv_cancel₀ hsK0, one_mul]
  have hn := nO_unif_pow hK hF h𝔭 hπ hπ' (vF 𝔭 D)
  rw [coe_ι] at hn
  rw [hGu]
  refine ⟨mul_mem_prime_power h𝔭 hPm hum, mul_ne_zero hP0 hu0, ?_⟩
  rw [nO_mul h𝔭 hPm hP0 hum, hn, nO_unit h𝔭 hum hui hu0, mul_one]
end Formalism.HermitianLattices.Ext.L3.D2
