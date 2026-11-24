-- Prove2me | solution 1 for Formalism.L2.Th1.F.IsogenySigmaQuotient.const_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T10:37:47.235729+00:00
-- url     : https://prove2.me/submissions/1da7eef2-4edd-4d02-807f-12b0dcc04494

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_TranslateProduct
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_IsogenySigma
import Theorems.Thm_Formalism_L2_Th1_F_IsogenySigmaQuotient_fac_analyticAt
import Theorems.Thm_Formalism_L2_Th1_F_IsogenySigmaQuotient_sg_eq_mul_dslope
import Theorems.Thm_Formalism_L2_Th1_F_IsogenySigmaQuotient_fac_zero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open Filter Topology
open scoped BigOperators ComplexConjugate
namespace Formalism.L2.Th1.F
namespace IsogenySigmaQuotient
variable (L : PeriodPair)
variable (α : ℂ) (S : Finset ℂ)
private lemma analyticAt_prod_fac (hb : SgStarBasic) (T : Finset ℂ) (z : ℂ) :
    AnalyticAt ℂ (fun w => ∏ P ∈ T, fac L P w) z := by
  refine Finset.induction_on T ?_ ?_
  · simp only [Finset.prod_empty]; exact analyticAt_const
  · intro a T ha ih
    have e : (fun w => ∏ P ∈ insert a T, fac L P w) = fun w => fac L a w * ∏ P ∈ T, fac L P w := by
      funext w; rw [Finset.prod_insert ha]
    rw [e]; exact (fac_analyticAt L hb a z).mul ih
end IsogenySigmaQuotient
end Formalism.L2.Th1.F
end
end

set_option autoImplicit false
noncomputable section
open Filter Topology
open scoped BigOperators ComplexConjugate
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.F
open Formalism.L2.Th1.F.IsogenySigmaQuotient
variable (L : PeriodPair)
variable (α : ℂ) (S : Finset ℂ)
namespace Formalism.L2.Th1.F.IsogenySigmaQuotient
theorem _root_.solution (hb : SgStarBasic) (hα : α ≠ 0) (hS : ∀ P ∈ S, P ∉ L.lattice) (c : ℂ)
    (h : ∀ z, num L α z = c * den L α S z) : c = 1 := by
  have hdiff : DifferentiableAt ℂ (sgStar L) 0 := (hb L).1 0
  have hdc : ContinuousAt (dslope (sgStar L) 0) 0 := continuousAt_dslope_same.2 hdiff
  have hd0 : dslope (sgStar L) 0 0 = 1 := by rw [dslope_same]; exact (hb L).2.2.2.1
  have g1c : ContinuousAt (fun w => dslope (sgStar L) 0 (α * w) ^ 2) 0 := by
    have h1 : ContinuousAt (fun w => dslope (sgStar L) 0 (α * w)) 0 :=
      ContinuousAt.comp_of_eq hdc (by fun_prop) (by simp)
    exact h1.pow 2
  have hprod : ContinuousAt (fun w => ∏ P ∈ S, fac L P w) 0 := (analyticAt_prod_fac L hb S 0).continuousAt
  have g2c : ContinuousAt (fun w => c * dslope (sgStar L) 0 w ^ 2 * ∏ P ∈ S, fac L P w) 0 :=
    (continuousAt_const.mul (hdc.pow 2)).mul hprod
  have heq : (fun w => dslope (sgStar L) 0 (α * w) ^ 2) =ᶠ[𝓝[≠] 0]
      (fun w => c * dslope (sgStar L) 0 w ^ 2 * ∏ P ∈ S, fac L P w) := by
    filter_upwards [self_mem_nhdsWithin] with w hw
    have hw' : w ≠ 0 := hw
    have hh := h w
    simp only [num, den] at hh
    rw [sg_eq_mul_dslope L hb (α * w), sg_eq_mul_dslope L hb w] at hh
    have hne : α ^ 2 * w ^ 2 ≠ 0 := mul_ne_zero (pow_ne_zero 2 hα) (pow_ne_zero 2 hw')
    apply mul_left_cancel₀ hne
    linear_combination hh
  have key := tendsto_nhds_unique (g1c.tendsto.mono_left nhdsWithin_le_nhds)
    ((g2c.tendsto.mono_left nhdsWithin_le_nhds).congr' heq.symm)
  simp only [mul_zero, hd0, one_pow, mul_one] at key
  rw [Finset.prod_congr rfl (fun P hP => fac_zero L hb P (hS P hP)), Finset.prod_const_one, mul_one] at key
  exact key.symm
end Formalism.L2.Th1.F.IsogenySigmaQuotient
