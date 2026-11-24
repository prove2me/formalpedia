-- Prove2me | solution 1 for Formalism.L2.SG.Pf.StdChar.psiStd_isChar
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T15:04:33.974857+00:00
-- url     : https://prove2.me/submissions/618d54b9-38a4-4a3b-ad98-697c5b2b3511

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_HaarTransversals_UnitaryHaarProducts_MeasCore
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_EmbeddingTraceSumAlt_NormUnitsOfCalculation
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FundamentalEquivalence_FundamentalContinuity_AdelicIsomorphismStatement
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_HaarTransversals_UnitaryHaarProducts_StdChar
import Theorems.Thm_Formalism_L2_SG_Pf_StdChar_norm_exp_real
import Theorems.Thm_Formalism_L2_SG_Pf_StdChar_continuous_psiA
import Theorems.Thm_Formalism_L2_SG_Pf_StdChar_psiFin_alg
import Theorems.Thm_Formalism_L2_SG_Pf_StdChar_norm_psiFin
import Theorems.Thm_Formalism_L2_SG_Pf_StdChar_continuous_psiFin
import Theorems.Thm_Formalism_L2_SG_Pf_StdChar_psiStd_apply
import Theorems.Thm_Formalism_L2_SG_Pf_StdChar_ext_alg
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Topology Filter
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.StdChar
variable (F : Type) [Field F] [NumberField F] [IsTotallyReal F]
namespace Formalism.L2.SG.Pf.StdChar
theorem _root_.solution : IsCharAF F (psiStd F) := by
  have hfun : (⇑(psiStd F) : AF F → ℂ) = fun x => psiA F x.1 * psiFin F x.2 := funext (psiStd_apply F)
  have hnA : ∀ y, ‖psiA F y‖ = 1 := fun y => by unfold psiA; exact norm_exp_real _
  have h3 : ∀ a : F, psiA F (algebraMap F (Ainf F) a) =
      Complex.exp (2 * Real.pi * Complex.I * ((trR F a : ℝ) : ℂ)) := by
    intro a
    simp only [psiA, ext_alg]
    rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hfun]
    exact ((continuous_psiA F).comp continuous_fst).mul ((continuous_psiFin F).comp continuous_snd)
  · intro x
    rw [psiStd_apply, norm_mul, hnA, norm_psiFin, one_mul]
  · intro a
    rw [psiStd_apply]
    have h1 : (algebraMap F (AF F) a).1 = algebraMap F (Ainf F) a := rfl
    have h2 : (algebraMap F (AF F) a).2 = algebraMap F (Af F) a := rfl
    rw [h1, h2, psiFin_alg, h3, ← Complex.exp_add]
    simp
  · set q : ℚ := 1 / (2 * (Fintype.card (InfinitePlace F) : ℚ)) with hqdef
    refine ⟨pairA F (algebraMap F (Ainf F) ((q : ℚ) : F)) 0, ?_⟩
    show psiA F (algebraMap F (Ainf F) ((q : ℚ) : F)) * psiFin F 0 ≠ 1
    rw [psiFin_zero, mul_one, h3]
    have hN : (Fintype.card (InfinitePlace F) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
    have hq : trR F ((q : ℚ) : F) = 1 / 2 := by
      show (∑ w : InfinitePlace F, (w.embedding ((q : ℚ) : F)).re) = 1 / 2
      simp only [map_ratCast, Complex.ratCast_re, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      rw [hqdef]
      push_cast
      field_simp
    rw [hq]
    have he : (2 * Real.pi * Complex.I * (((1 / 2 : ℝ)) : ℂ)) = Real.pi * Complex.I := by
      push_cast
      ring
    rw [he, Complex.exp_pi_mul_I]
    norm_num
end Formalism.L2.SG.Pf.StdChar
