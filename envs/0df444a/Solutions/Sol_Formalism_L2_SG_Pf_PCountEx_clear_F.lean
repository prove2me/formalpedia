-- Prove2me | solution 1 for Formalism.L2.SG.Pf.PCountEx.clear_F
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T07:17:37.919897+00:00
-- url     : https://prove2.me/submissions/a32e7f63-4a8b-4f48-a22a-5848c20d87cd

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_WithZeroLeOneEqExp
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_IotaFIntMem
import Theorems.Thm_Formalism_L2_SG_Pf_PCountEx_iotaF_int_mem
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
noncomputable section
open scoped Classical
open NumberField IsDedekindDomain ValuativeRel
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.PCountEx
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E}
  (A : ∀ p : HeightOneSpectrum (𝓞 F), Formalism.MainNotions.S.Loc.LocAt F E sig p)
namespace Formalism.L2.SG.Pf.PCountEx
theorem _root_.solution (p : HeightOneSpectrum (𝓞 F)) (l : (A p).Fp) :
    ∃ t : 𝓞 F, t ≠ 0 ∧ (A p).ιF (algebraMap (𝓞 F) F t) * l ∈ (haveI := (A p).lf; 𝒪[(A p).Fp]) := by
  haveI := (A p).lf
  by_cases hl : l = 0
  · refine ⟨1, one_ne_zero, ?_⟩
    rw [hl, mul_zero]
    exact Subring.zero_mem _
  obtain ⟨π, hπp, hπ0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot p.ne_bot
  have hπv : p.valuation F (algebraMap (𝓞 F) F π) < 1 := by
    first
    | exact (p.valuation_lt_one_iff_mem π).2 hπp
    | exact (p.valuation_lt_one_iff_mem (K := F) π).2 hπp
  have hπF0 : algebraMap (𝓞 F) F π ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 F) F)).2 hπ0
  obtain ⟨c, hc⟩ : ∃ c, c = (A p).ιF (algebraMap (𝓞 F) F π) := ⟨_, rfl⟩
  have hcint : c ∈ (ValuativeRel.valuation (A p).Fp).integer := by
    rw [hc]
    exact iotaF_int_mem A p π
  have hc0 : c ≠ 0 := by
    rw [hc]
    exact (map_ne_zero (A p).ιF).2 hπF0
  have hnot : -(c⁻¹) ∉ (ValuativeRel.valuation (A p).Fp).integer := by
    intro hmem
    rw [Valuation.mem_integer_iff] at hmem
    have h1 := (Valuation.vle_one_iff (ValuativeRel.valuation (A p).Fp)).2 hmem
    have h2 : -(c⁻¹) = (A p).ιF (-(algebraMap (𝓞 F) F π)⁻¹) := by rw [hc, map_neg, map_inv₀]
    rw [h2, ← map_one (A p).ιF, (A p).val, map_one] at h1
    have h3 : p.valuation F (algebraMap (𝓞 F) F π) * p.valuation F (-(algebraMap (𝓞 F) F π)⁻¹) = 1 := by
      rw [← map_mul, mul_neg, mul_inv_cancel₀ hπF0, Valuation.map_neg, map_one]
    have h4 : p.valuation F (algebraMap (𝓞 F) F π) * p.valuation F (-(algebraMap (𝓞 F) F π)⁻¹) ≤
        p.valuation F (algebraMap (𝓞 F) F π) * 1 := by
      first
      | gcongr
      | exact mul_le_mul_right' h1 _
      | exact mul_le_mul_of_nonneg_left h1 (zero_le _)
    rw [h3, mul_one] at h4
    exact absurd h4 (not_le.2 hπv)
  have hW : IsOpen ((fun z => (z * l - 1) * c⁻¹) ⁻¹'
      ((ValuativeRel.valuation (A p).Fp).integer : Set (A p).Fp)) :=
    Valuation.isOpen_integer.preimage (((continuous_mul_right l).sub continuous_const).mul continuous_const)
  have hne : ((fun z => (z * l - 1) * c⁻¹) ⁻¹'
      ((ValuativeRel.valuation (A p).Fp).integer : Set (A p).Fp)).Nonempty := by
    refine ⟨l⁻¹, ?_⟩
    show (l⁻¹ * l - 1) * c⁻¹ ∈ (ValuativeRel.valuation (A p).Fp).integer
    rw [inv_mul_cancel₀ hl, sub_self, zero_mul]
    exact Subring.zero_mem _
  obtain ⟨y, hy⟩ := (A p).dense.exists_mem_open hW hne
  have hy' : ((A p).ιF y * l - 1) * c⁻¹ ∈ (ValuativeRel.valuation (A p).Fp).integer := hy
  have hy1 : (A p).ιF y * l ∈ (ValuativeRel.valuation (A p).Fp).integer := by
    have e : (A p).ιF y * l = ((A p).ιF y * l - 1) * c⁻¹ * c + 1 := by
      rw [mul_assoc, inv_mul_cancel₀ hc0, mul_one, sub_add_cancel]
    rw [e]
    exact Subring.add_mem _ (Subring.mul_mem _ hy' hcint) (Subring.one_mem _)
  have hy0 : (A p).ιF y ≠ 0 := by
    intro h0
    rw [h0, zero_mul, zero_sub, neg_mul, one_mul] at hy'
    exact hnot hy'
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 F) y
  have hb' : algebraMap (𝓞 F) F b ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb
  have hy0' : (A p).ιF (algebraMap (𝓞 F) F a / algebraMap (𝓞 F) F b) ≠ 0 := hy0
  refine ⟨a, ?_, ?_⟩
  · rintro rfl
    apply hy0'
    simp
  · have e : algebraMap (𝓞 F) F a =
        algebraMap (𝓞 F) F b * (algebraMap (𝓞 F) F a / algebraMap (𝓞 F) F b) := by
      field_simp
    rw [e, map_mul, mul_assoc]
    exact Subring.mul_mem _ (iotaF_int_mem A p b) hy1
end Formalism.L2.SG.Pf.PCountEx
