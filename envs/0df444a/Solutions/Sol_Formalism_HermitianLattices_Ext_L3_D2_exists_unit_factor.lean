-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.D2.exists_unit_factor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T10:18:42.599793+00:00
-- url     : https://prove2.me/submissions/2f406f16-0645-40fe-9c34-ea31c5721b6e

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsMulEqUnifPow
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_MulMemPrimePower
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_D2_exists_dvd_mul
import Theorems.Thm_P2M_Formalism_HermitianLattices_Ext_L3_D2_coe___fedd4e958df8
import Theorems.Thm_P2M_Formalism_HermitianLattices_Ext_L3_D2_c__ne_zero_3faafbcab9f8
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_D2_mem_pK_zero_of_mul
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_D2_mem_pK
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_D2_mem_pK_iff_unif
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_idealPowerSpanBounds_mem_pow_iff
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_idealPowerSpanBounds_ne_bot
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_localValuationFiltration_mem_pow_vF
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_localValuationFiltration_notMem_pow_vF


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
theorem _root_.solution {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {π : 𝓞 F} (hπ : π ∈ 𝔭)
    (hπ' : π ∉ 𝔭 ^ 2) {D : 𝓞 F} (hD0 : D ≠ 0) :
    ∃ w : K, w ∈ pK K 𝔭 0 ∧ w⁻¹ ∈ pK K 𝔭 0 ∧ w ≠ 0 ∧
      algebraMap (𝓞 K) K (ι D) = algebraMap (𝓞 K) K (ι π) ^ vF 𝔭 D * w := by
  have hpr := h𝔭.isPrime
  have hp0 : 𝔭 ≠ ⊥ := idealPowerSpanBounds.ne_bot h𝔭
  have hπ0 : π ≠ 0 := fun h0 => hπ' (h0 ▸ zero_mem _)
  have hDv : algebraMap (𝓞 K) K (ι D) ∈ pK K 𝔭 (vF 𝔭 D) :=
    (mem_pK h𝔭).2 ⟨1, fun h1 => hpr.ne_top ((Ideal.eq_top_iff_one _).2 h1), ι D,
      (idealPowerSpanBounds.mem_pow_iff 𝔭 _ D).2 (localValuationFiltration.mem_pow_vF h𝔭 hD0), by
        rw [coe_ι, map_one, map_one, one_mul]⟩
  obtain ⟨w, hw, ew⟩ := (mem_pK_iff_unif h𝔭 hπ hπ').1 hDv
  rw [coe_ι] at ew
  obtain ⟨t1, ht1, r1, er1⟩ := exists_dvd_mul hpr hp0 (Ideal.pow_mem_pow hπ (vF 𝔭 D))
    (localValuationFiltration.notMem_pow_vF h𝔭 hD0)
  have hP0 : algebraMap (𝓞 K) K (ι π) ^ vF 𝔭 D ≠ 0 := pow_ne_zero _ (cι_ne_zero hπ0)
  have hDK0 := cι_ne_zero (K := K) hD0
  have hw0 : w ≠ 0 := by
    rintro rfl
    rw [mul_zero] at ew
    exact hDK0 ew
  have er1' : algebraMap (𝓞 K) K (ι t1) * algebraMap (𝓞 K) K (ι π) ^ vF 𝔭 D =
      algebraMap (𝓞 K) K (ι D) * algebraMap (𝓞 K) K (ι r1) := by
    rw [← map_pow, ← map_mul, ← map_mul, ← map_pow, ← map_mul, ← map_mul, er1]
  refine ⟨w, hw, ?_, hw0, ew⟩
  refine mem_pK_zero_of_mul h𝔭 ht1 (z := ι r1) ?_
  rw [ew] at er1'
  have h2 : algebraMap (𝓞 K) K (ι t1) = w * algebraMap (𝓞 K) K (ι r1) :=
    mul_left_cancel₀ hP0 (by linear_combination er1')
  rw [h2, mul_comm w, mul_assoc, mul_inv_cancel₀ hw0, mul_one]
end Formalism.HermitianLattices.Ext.L3.D2
