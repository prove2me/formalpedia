-- Prove2me | solution 1 for Formalism.L2.SG.Pf.LocalDenominators.exists_den
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:04:34.061559+00:00
-- url     : https://prove2.me/submissions/ba2a79a3-8c21-4b18-8a7f-7ba28f9a5faf

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_PsiEDef
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_ExistsDenOfLeOne
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_LocalDenominators
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_FiniteUnitaryColumns_emb_succ_succ
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_FiniteUnitaryColumns_emb_succ_zero
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_FiniteUnitaryColumns_emb_zero_succ
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_FiniteUnitaryColumns_emb_zero_zero
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_IsUnif0_ne_zero
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_localValuationFiltration_mem_pow_vF
import Theorems.Thm_Formalism_L2_SG_Pf_G2_exists_mul_mem_span
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
namespace Formalism.L2.SG.Pf.LocalDenominators
theorem _root_.solution {a : F} (ha : p.valuation F a ≤ 1) :
    ∃ t : 𝓞 F, t ∉ p.asIdeal ∧ ∃ y : 𝓞 F, (y : F) = (t : F) * a := by
  obtain ⟨r, s, hs, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 F) a
  have hs0 : s ≠ 0 := nonZeroDivisors.ne_zero hs
  have hs0' : ((s : 𝓞 F) : F) ≠ 0 := by exact_mod_cast hs0
  rw [map_div₀, valuation_of_algebraMap, valuation_of_algebraMap] at ha
  have hpos : 0 < p.intValuation s := by
    rw [zero_lt_iff]
    exact (intValuation_ne_zero p s hs0)
  have hrs : p.intValuation r ≤ p.intValuation s := by
    rwa [div_le_one₀ hpos] at ha
  have hr : r ∈ p.asIdeal ^ Formalism.HermitianLattices.Ext.L3.vF p.asIdeal s := by
    rw [← intValuation_le_pow_iff_mem]
    exact hrs.trans ((intValuation_le_pow_iff_mem p s _).2
      (Formalism.HermitianLattices.Ext.L3.localValuationFiltration.mem_pow_vF p.isMaximal hs0))
  obtain ⟨t, ht, hmul⟩ := Formalism.L2.SG.Pf.G2.exists_mul_mem_span p.isMaximal hs0
  obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.1 (hmul r hr)
  refine ⟨t, ht, y, ?_⟩
  have h := congrArg (algebraMap (𝓞 F) F) hy
  simp only [map_mul] at h
  field_simp
  rw [mul_comm] at h
  simpa [mul_comm] using h
end Formalism.L2.SG.Pf.LocalDenominators
