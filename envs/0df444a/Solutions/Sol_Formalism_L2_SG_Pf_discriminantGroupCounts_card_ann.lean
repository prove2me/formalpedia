-- Prove2me | solution 1 for Formalism.L2.SG.Pf.discriminantGroupCounts.card_ann
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:11:38.684053+00:00
-- url     : https://prove2.me/submissions/d3d8643b-8a2f-4856-8431-2da1d841338c

import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_DiscOnto
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_DiagMulMulDiagApply
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_DiscriminantGroupCounts
import Theorems.Thm_Formalism_L2_SG_Pf_discriminantGroupCounts_mul_mk_eq_zero_iff
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_U3_absNorm_extP_pow
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_idealPowerSpanBounds_absNorm_extP_pow


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
namespace Formalism.L2.SG.Pf.discriminantGroupCounts
theorem _root_.solution (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal)
    {a : 𝓞 F} {e k : ℕ} (ha : a ∈ 𝔭 ^ e) (ha' : a ∉ 𝔭 ^ (e + 1)) (hek : e ≤ k) :
    Nat.card {z : 𝓞 K ⧸ extP K 𝔭 ^ k // z * Ideal.Quotient.mk (extP K 𝔭 ^ k) (ι a) = 0} =
      Ideal.absNorm 𝔭 ^ (2 * e) := by
  have hle : extP K 𝔭 ^ k ≤ extP K 𝔭 ^ (k - e) := Ideal.pow_le_pow_right (Nat.sub_le k e)
  let π : 𝓞 K ⧸ extP K 𝔭 ^ k →+* 𝓞 K ⧸ extP K 𝔭 ^ (k - e) :=
    Ideal.Quotient.lift (extP K 𝔭 ^ k) (Ideal.Quotient.mk (extP K 𝔭 ^ (k - e)))
      (fun w hw => Ideal.Quotient.eq_zero_iff_mem.mpr (hle hw))
  have hπ : Function.Surjective π := by
    intro y
    obtain ⟨w, rfl⟩ := Ideal.Quotient.mk_surjective y
    exact ⟨Ideal.Quotient.mk _ w, Ideal.Quotient.lift_mk _ _ _⟩
  have hS : Nat.card {z : 𝓞 K ⧸ extP K 𝔭 ^ k // z * Ideal.Quotient.mk (extP K 𝔭 ^ k) (ι a) = 0} =
      Nat.card π.toAddMonoidHom.ker := by
    refine Nat.card_congr (Equiv.subtypeEquivRight fun z => ?_)
    obtain ⟨w, rfl⟩ := Ideal.Quotient.mk_surjective z
    rw [mul_mk_eq_zero_iff h𝔭 ha ha' hek, AddMonoidHom.mem_ker]
    exact Ideal.Quotient.eq_zero_iff_mem.symm
  have hcard := AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup π.toAddMonoidHom.ker
  rw [Nat.card_congr (QuotientAddGroup.quotientKerEquivOfSurjective π.toAddMonoidHom hπ).toEquiv,
    Formalism.HermitianLattices.Ext.L3.idealPowerSpanBounds.absNorm_extP_pow hK hF h𝔭,
    Formalism.HermitianLattices.Ext.L3.idealPowerSpanBounds.absNorm_extP_pow hK hF h𝔭, ← hS] at hcard
  have hN : Ideal.absNorm 𝔭 ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]
    exact Ring.ne_bot_of_isMaximal_of_not_isField h𝔭 (NumberField.RingOfIntegers.not_isField F)
  have h2 : Ideal.absNorm 𝔭 ^ (2 * k) =
      Ideal.absNorm 𝔭 ^ (2 * (k - e)) * Ideal.absNorm 𝔭 ^ (2 * e) := by
    rw [← pow_add]
    congr 1
    omega
  rw [h2] at hcard
  exact (Nat.eq_of_mul_eq_mul_left (pow_pos (Nat.pos_of_ne_zero hN) _) hcard).symm
end Formalism.L2.SG.Pf.discriminantGroupCounts
