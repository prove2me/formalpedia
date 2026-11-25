-- Prove2me | solution 1 for Formalism.L2.SG.Pf.discriminantGroupCounts.kerCount_main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:50:45.053801+00:00
-- url     : https://prove2.me/submissions/3dfd84df-ccc7-4a92-ad94-4a929ced77bb

import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_DiscOnto
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_DiagMulMulDiagApply
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_DiscriminantGroupCounts
import Theorems.Thm_Formalism_L2_SG_Pf_discriminantGroupCounts_card_ann
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_BoxSum_finite_quot
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_LIOrb_finite_quot
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_NormResidues_finite_quot
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_idealPowerSpanBounds_finite_quot
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_idealPowerSpanBounds_mem_of_mul_mem
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_idealPowerSpanBounds_mul_notMem
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_idealPowerSpanBounds_ne_bot
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_idealPowerSpanBounds_star_mk
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_localValuationFiltration_mem_pow_vF
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_localValuationFiltration_notMem_pow_vF
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_reductionMapsOfForms_exists_unit_quot
import Theorems.Thm_Formalism_L2_SG_Pf_discriminantGroupCounts_card_kerX_eq
import Theorems.Thm_Formalism_L2_SG_Pf_discriminantGroupCounts_diag_mul_mul_diag_apply


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module Matrix
open scoped Formalism.HermitianLattices.Ext.L3.idealPowerSpanBounds
noncomputable section
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.discriminantGroupCounts
open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt Formalism.L2.SG.Pf.G5
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
local notation "ι" => algebraMap (𝓞 F) (𝓞 K)
variable [Fact (IsFixF K F)]
namespace Formalism.L2.SG.Pf.discriminantGroupCounts
theorem _root_.solution (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {m : ℕ}
    {a : Fin m → 𝓞 F} (ha0 : ∀ i, a i ≠ 0) {k : ℕ} (hk : 2 * vJof 𝔭 a + 1 ≤ k) (N : ℕ)
    (hN : ∀ T : Matrix (Fin m) (Fin m) (𝓞 K ⧸ extP K 𝔭 ^ k), Tᴴ = T →
      (∀ i j, T i j ∈ (extP K 𝔭).map (Ideal.Quotient.mk (extP K 𝔭 ^ k))) →
      Nat.card {Y : Matrix (Fin m) (Fin m) (𝓞 K ⧸ extP K 𝔭 ^ k) // phiQ K 𝔭 k a Y = T} = N) :
    Nat.card (kerSet K 𝔭 k a) = N := by
  have hF : IsFixF K F := Fact.out
  have hfin : Finite (𝓞 K ⧸ extP K 𝔭 ^ k) := idealPowerSpanBounds.finite_quot h𝔭 k
  let e : Fin m → ℕ := fun i => vF 𝔭 (a i)
  have hmem : ∀ i, a i ∈ 𝔭 ^ e i := fun i => localValuationFiltration.mem_pow_vF h𝔭 (ha0 i)
  have hnot : ∀ i, a i ∉ 𝔭 ^ (e i + 1) := fun i => localValuationFiltration.notMem_pow_vF h𝔭 (ha0 i)
  have hle : ∀ i, e i ≤ vJof 𝔭 a := fun i =>
    Finset.single_le_sum (f := fun j => vF 𝔭 (a j)) (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
  have hsum : ∀ i j, e i + e j + 1 ≤ k := fun i j => by
    have := hle i; have := hle j; omega
  let d : Fin m → 𝓞 K ⧸ extP K 𝔭 ^ k := fun i => Ideal.Quotient.mk (extP K 𝔭 ^ k) (ι (a i))
  have hd : ∀ i, star (d i) = d i := fun i => by
    show star (Ideal.Quotient.mk (extP K 𝔭 ^ k) (ι (a i))) = _
    rw [idealPowerSpanBounds.star_mk]
    exact congrArg _ (idealPowerSpanBounds.conjO_map hF (a i))
  have hprod : ∀ i j (z : 𝓞 K ⧸ extP K 𝔭 ^ k),
      d i * z * d j = z * Ideal.Quotient.mk (extP K 𝔭 ^ k) (ι (a i * a j)) := fun i j z => by
    show Ideal.Quotient.mk _ (ι (a i)) * z * Ideal.Quotient.mk _ (ι (a j)) = _
    rw [map_mul, map_mul]
    ring
  have hpm : ∀ i j, a i * a j ∈ 𝔭 ^ (e i + e j) := fun i j => by
    rw [pow_add]; exact Ideal.mul_mem_mul (hmem i) (hmem j)
  have hpn : ∀ i j, a i * a j ∉ 𝔭 ^ (e i + e j + 1) := fun i j =>
    idealPowerSpanBounds.mul_notMem h𝔭.isPrime (idealPowerSpanBounds.ne_bot h𝔭) (hnot i) (hnot j)
  obtain ⟨θ, u, hu⟩ := reductionMapsOfForms.exists_unit_quot (K := K) hK h𝔭 k
  have hsq : ∀ i j, Nat.card {z // d i * z * d j = 0} =
      Nat.card {z // z * d i = 0} * Nat.card {z // z * d j = 0} := fun i j => by
    rw [Nat.card_congr (Equiv.subtypeEquivRight fun z => by rw [hprod i j z]),
      card_ann hK hF h𝔭 (hpm i j) (hpn i j) (by have := hsum i j; omega),
      card_ann hK hF h𝔭 (hmem i) (hnot i) (by have := hsum i i; omega),
      card_ann hK hF h𝔭 (hmem j) (hnot j) (by have := hsum j j; omega), ← pow_add]
    congr 1
    ring
  have hent : ∀ T ∈ tSet d, ∀ i j, T i j ∈ (extP K 𝔭).map (Ideal.Quotient.mk (extP K 𝔭 ^ k)) := by
    intro T hT i j
    obtain ⟨w, hw⟩ := Ideal.Quotient.mk_surjective (T i j)
    have h0 : d i * T i j * d j = 0 := by
      rw [← diag_mul_mul_diag_apply, hT.2, Matrix.zero_apply]
    rw [hprod, ← hw, ← map_mul, Ideal.Quotient.eq_zero_iff_mem] at h0
    have h1 : ι (a i * a j) * w ∈ extP K 𝔭 ^ ((e i + e j) + 1) := by
      rw [mul_comm]; exact Ideal.pow_le_pow_right (hsum i j) h0
    have h2 := idealPowerSpanBounds.mem_of_mul_mem h𝔭 (hpn i j) h1
    rw [pow_one] at h2
    rw [← hw]
    exact Ideal.mem_map_of_mem _ h2
  exact card_kerX_eq hd hu hsq N fun T hT => hN T hT.1 (hent T hT)
end Formalism.L2.SG.Pf.discriminantGroupCounts
