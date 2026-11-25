-- Prove2me | solution 1 for Formalism.L2.SG.Pf.LocalDenominators.iE_mem_O_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:57:47.253384+00:00
-- url     : https://prove2.me/submissions/2f7e0c4a-aabb-488b-bc2b-80fd8d9124bd

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_PsiEDef
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_ExistsDenOfLeOne
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_LocalDenominators
import Theorems.Thm_Formalism_L2_SG_Pf_LocalDenominators_iF_mem_iff
import Theorems.Thm_Formalism_L2_SG_Pf_LocalDenominators_iF_unit
import Theorems.Thm_Formalism_L2_SG_Pf_LocalDenominators_exists_den
import Theorems.Thm_Formalism_L2_SG_Pf_LocalDenominators_iE_int
import Theorems.Thm_Formalism_L2_SG_Pf_LocalDenominators_iE_alg
import Theorems.Thm_Formalism_L2_SG_Pf_LocalDenominators_alg_mem_O
import Theorems.Thm_Formalism_L2_SG_Pf_LocalDenominators_mem_of_alg_mem_O
import Theorems.Thm_Formalism_L2_SG_Pf_LocalDenominators_iE_sig_mem
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_FiniteUnitaryColumns_emb_succ_succ
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_FiniteUnitaryColumns_emb_succ_zero
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_FiniteUnitaryColumns_emb_zero_succ
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_FiniteUnitaryColumns_emb_zero_zero
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
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
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum ValuativeRel Polynomial
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.LocalDenominators
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {sig : E →ₐ[F] E} {p : HeightOneSpectrum (𝓞 F)} (A : Formalism.MainNotions.S.Loc.LocAt F E sig p)
variable (hσ : ∀ e, sig (sig e) = e) (hfix : ∀ y : E, sig y = y → y ∈ (algebraMap F E).range)
include hσ hfix
namespace Formalism.L2.SG.Pf.LocalDenominators
theorem _root_.solution (x : E) :
    A.ιE x ∈ A.O ↔ ∃ s : 𝓞 F, s ∉ p.asIdeal ∧ IsIntegral ℤ (algebraMap F E (s : F) * x) := by
  constructor
  · intro hx

    obtain ⟨t, ht⟩ := hfix (x + sig x) (by rw [map_add, hσ, add_comm])
    obtain ⟨n, hn⟩ := hfix (x * sig x) (by rw [map_mul, hσ, mul_comm])
    have hxs := iE_sig_mem A hσ hfix hx
    have htO : A.ιF t ∈ 𝒪[A.Fp] := by
      apply mem_of_alg_mem_O A
      rw [← iE_alg, ht, map_add]; exact A.O.add_mem hx hxs
    have hnO : A.ιF n ∈ 𝒪[A.Fp] := by
      apply mem_of_alg_mem_O A
      rw [← iE_alg, hn, map_mul]; exact A.O.mul_mem hx hxs
    obtain ⟨s₁, hs₁, y₁, hy₁⟩ := exists_den ((iF_mem_iff A t).1 htO)
    obtain ⟨s₂, hs₂, y₂, hy₂⟩ := exists_den ((iF_mem_iff A n).1 hnO)
    refine ⟨s₁ * s₂, fun h => (p.isPrime.mem_or_mem h).elim hs₁ hs₂, ?_⟩
    set c : E := algebraMap F E ((s₁ * s₂ : 𝓞 F) : F) with hc
    have hkey : (c * x) ^ 2 - algebraMap F E ((s₂ * y₁ : 𝓞 F) : F) * (c * x) +
        algebraMap F E ((s₁ * s₁ * s₂ * y₂ : 𝓞 F) : F) = 0 := by
      have hy₁' : algebraMap (𝓞 F) F y₁ = algebraMap (𝓞 F) F s₁ * t := hy₁
      have hy₂' : algebraMap (𝓞 F) F y₂ = algebraMap (𝓞 F) F s₂ * n := hy₂
      have e1 : algebraMap F E ((s₂ * y₁ : 𝓞 F) : F) = c * (x + sig x) := by
        rw [hc, ← ht, ← map_mul]; congr 1
        show algebraMap (𝓞 F) F (s₂ * y₁) = algebraMap (𝓞 F) F (s₁ * s₂) * t
        rw [map_mul, map_mul, hy₁']; ring
      have e2 : algebraMap F E ((s₁ * s₁ * s₂ * y₂ : 𝓞 F) : F) = c * c * (x * sig x) := by
        rw [hc, ← hn, ← map_mul, ← map_mul]; congr 1
        show algebraMap (𝓞 F) F (s₁ * s₁ * s₂ * y₂) = algebraMap (𝓞 F) F (s₁ * s₂) * algebraMap (𝓞 F) F (s₁ * s₂) * n
        rw [map_mul, map_mul, map_mul, map_mul, hy₂']; ring
      rw [e1, e2]; ring
    have hint : IsIntegral (𝓞 F) (c * x) := by
      refine ⟨X ^ 2 - C (s₂ * y₁) * X + C (s₁ * s₁ * s₂ * y₂), ?_, ?_⟩
      · monicity!
      · rw [← hkey]
        simp [eval₂_sub, eval₂_add, eval₂_mul, eval₂_X, eval₂_C, eval₂_pow]
        rfl
    exact isIntegral_trans (R := ℤ) _ hint
  · rintro ⟨s, hs, hint⟩
    have h1 := iE_int A hint
    rw [map_mul, iE_alg] at h1
    have hinv : (A.ιF (s : F))⁻¹ ∈ 𝒪[A.Fp] := by
      rw [Valuation.mem_integer_iff, map_inv₀, iF_unit A hs, inv_one]
    have hne : A.ιF (s : F) ≠ 0 := by
      intro h0; have := iF_unit A hs; rw [h0, map_zero] at this; exact zero_ne_one this
    have e : A.ιE x = algebraMap A.Fp A.Ep (A.ιF (s : F))⁻¹ * (algebraMap A.Fp A.Ep (A.ιF (s : F)) * A.ιE x) := by
      rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ hne, map_one, one_mul]
    rw [e]
    exact A.O.mul_mem (alg_mem_O A hinv) h1
end Formalism.L2.SG.Pf.LocalDenominators
