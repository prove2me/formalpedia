-- Prove2me | solution 1 for Formalism.L2.SG.Pf.UnitPairSolutions.unit_part
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:25:04.240191+00:00
-- url     : https://prove2.me/submissions/91e6d561-50e4-46ea-8b06-42213085636e

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_InPOfMemPow
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_StarAlgebraMap
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_SmulMemLocFOfSP
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_BallB_IsStep_change
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_FiniteUnitaryColumns_emb_succ_succ
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_FiniteUnitaryColumns_emb_succ_zero
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_FiniteUnitaryColumns_emb_zero_succ
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_FiniteUnitaryColumns_emb_zero_zero
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_InP_mem_SP
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_IsUnif0_ne_zero
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_mem_SP
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_U0_Dv_mem
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_WCA_InL_mem
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_idealPowerSpanBounds_mul_notMem
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.H.dualEquiv_apply
attribute [local simp] Formalism.HermitianLattices.Ext.L3.FiniteUnitaryColumns.emb_succ_succ
attribute [local simp] Formalism.HermitianLattices.Ext.L3.FiniteUnitaryColumns.emb_succ_zero
attribute [local simp] Formalism.HermitianLattices.Ext.L3.FiniteUnitaryColumns.emb_zero_succ
attribute [local simp] Formalism.HermitianLattices.Ext.L3.FiniteUnitaryColumns.emb_zero_zero


section
open NumberField Module
noncomputable section
namespace Formalism.L2.SG.Pf.UnitPairSolutions
open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt Formalism.HermitianLattices.Ext.L3.HU Formalism.L2.SG.Pf.GluingBases
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
private theorem mem_pow_vF_of_ne_zero {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {a : 𝓞 F} (ha : a ≠ 0) :
    a ∈ 𝔭 ^ vF 𝔭 a ∧ a ∉ 𝔭 ^ (vF 𝔭 a + 1) := by
  have hex : ∃ j, a ∉ 𝔭 ^ j := by
    by_contra h
    push_neg at h
    have hi : a ∈ ⨅ i : ℕ, 𝔭 ^ i := (Submodule.mem_iInf _).mpr h
    rw [Ideal.iInf_pow_eq_bot_of_isDomain 𝔭 h𝔭.ne_top] at hi
    exact ha ((Submodule.mem_bot _).mp hi)
  obtain ⟨j, hj⟩ := hex
  have hbdd : BddAbove {e : ℕ | a ∈ 𝔭 ^ e} := by
    refine ⟨j, fun e he => ?_⟩
    by_contra hlt
    push_neg at hlt
    exact hj (Ideal.pow_le_pow_right hlt.le he)
  refine ⟨Nat.sSup_mem ⟨0, by simp⟩ hbdd, fun h => ?_⟩
  have hc := le_csSup hbdd (show vF 𝔭 a + 1 ∈ {e : ℕ | a ∈ 𝔭 ^ e} from h)
  change vF 𝔭 a + 1 ≤ vF 𝔭 a at hc
  omega
section Vec
variable {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
end Vec
end Formalism.L2.SG.Pf.UnitPairSolutions
end
end

set_option autoImplicit false
open NumberField Module
noncomputable section
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.UnitPairSolutions
open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt Formalism.HermitianLattices.Ext.L3.HU Formalism.L2.SG.Pf.GluingBases
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
namespace Formalism.L2.SG.Pf.UnitPairSolutions
theorem _root_.solution (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal)
    {π s₀ : 𝓞 F} (hu : IsUnif0 𝔭 π s₀) {a : 𝓞 F} (ha : a ≠ 0) :
    (algebraMap F K (a : F))⁻¹ * algebraMap F K (π : F) ^ vF 𝔭 a ∈ SP K 𝔭 := by
  haveI := h𝔭.isPrime
  obtain ⟨hmem, hnot⟩ := mem_pow_vF_of_ne_zero h𝔭 ha
  have hle : Ideal.span {s₀ ^ vF 𝔭 a} * 𝔭 ^ vF 𝔭 a ≤ Ideal.span {π ^ vF 𝔭 a} := by
    rw [← Ideal.span_singleton_pow, ← Ideal.span_singleton_pow, ← mul_pow]
    exact Ideal.pow_right_mono hu.le _
  have hsa : s₀ ^ vF 𝔭 a * a ∈ Ideal.span {π ^ vF 𝔭 a} :=
    hle (Ideal.mul_mem_mul (Ideal.mem_span_singleton_self _) hmem)
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.mp hsa
  have hne : 𝔭 ≠ ⊥ := (Submodule.ne_bot_iff _).mpr ⟨π, hu.mem, hu.ne_zero⟩
  have hbnot : b ∉ 𝔭 := by
    intro hb𝔭
    have h1 : s₀ ^ vF 𝔭 a * a ∈ 𝔭 ^ (0 + vF 𝔭 a + 1) := by
      rw [← hb, zero_add, pow_succ, mul_comm b]
      exact Ideal.mul_mem_mul (Ideal.pow_mem_pow hu.mem _) hb𝔭
    refine idealPowerSpanBounds.mul_notMem h𝔭.isPrime hne ?_ hnot h1
    rw [zero_add, pow_one]
    exact fun h => hu.s_notMem (h𝔭.isPrime.mem_of_pow_mem _ h)
  have hbK : algebraMap F K (b : F) * algebraMap F K (π : F) ^ vF 𝔭 a =
      algebraMap F K (s₀ : F) ^ vF 𝔭 a * algebraMap F K (a : F) := by
    have := congrArg (fun x : 𝓞 F => algebraMap F K (x : F)) hb
    simpa [map_mul, map_pow] using this
  have haK : algebraMap F K (a : F) ≠ 0 := by simpa using ha
  refine mem_SP.mpr ⟨b, hbnot, algebraMap (𝓞 F) (𝓞 K) (s₀ ^ vF 𝔭 a), ?_⟩
  show algebraMap F K ((s₀ ^ vF 𝔭 a : 𝓞 F) : F) =
    algebraMap F K (b : F) * ((algebraMap F K (a : F))⁻¹ * algebraMap F K (π : F) ^ vF 𝔭 a)
  have hc : ((s₀ ^ vF 𝔭 a : 𝓞 F) : F) = (s₀ : F) ^ vF 𝔭 a := by simp
  rw [hc, map_pow, ← mul_assoc, mul_comm (algebraMap F K (b : F)), mul_assoc, hbK]
  field_simp
end Formalism.L2.SG.Pf.UnitPairSolutions
