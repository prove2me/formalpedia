-- Prove2me | solution 1 for Formalism.L2.SG.Pf.LocalDenominators.mem_of_alg_mem_O
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:39:38.562539+00:00
-- url     : https://prove2.me/submissions/3545e447-285d-4644-9409-7c9a18d71b38

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_PsiEDef
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_ExistsDenOfLeOne
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_LocalDenominators
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
namespace Formalism.L2.SG.Pf.LocalDenominators
theorem _root_.solution {z : A.Fp} (hz : algebraMap A.Fp A.Ep z ∈ A.O) : z ∈ 𝒪[A.Fp] := by
  have h1 := (A.O_def _).mp hz
  have h2 : IsIntegral 𝒪[A.Fp] z :=
    (isIntegral_algHom_iff (IsScalarTower.toAlgHom 𝒪[A.Fp] A.Fp A.Ep)
      (algebraMap A.Fp A.Ep).injective).mp h1
  first
  | exact (Valuation.integer.integers _).mem_of_integral h2
  | simpa using (Valuation.integer.integers _).mem_of_integral h2
end Formalism.L2.SG.Pf.LocalDenominators
