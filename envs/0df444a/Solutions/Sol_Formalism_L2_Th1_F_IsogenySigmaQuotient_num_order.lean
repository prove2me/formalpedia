-- Prove2me | solution 1 for Formalism.L2.Th1.F.IsogenySigmaQuotient.num_order
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T10:25:03.858532+00:00
-- url     : https://prove2.me/submissions/82d03bc1-094c-4643-91ef-97e83c796cba

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_TranslateProduct
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_IsogenySigma
import Theorems.Thm_Formalism_L2_Th1_F_IsogenySigmaQuotient_sg_order
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
private lemma add_self_eq_two_mul_extended_int (x : WithTop ℤ) : x + x = 2 * x := by
  cases x with
  | top => first | rfl | decide | simp
  | coe a =>
    rw [← WithTop.coe_add, show (2 : WithTop ℤ) = ((2 : ℤ) : WithTop ℤ) from rfl, ← WithTop.coe_mul,
      two_mul]
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
theorem _root_.solution (hord : SigmaOrder) (he : SigmaEntire) (hb : SgStarBasic) (hα : α ≠ 0) (z : ℂ) :
    meromorphicOrderAt (num L α) z = 2 * ind L (α * z) := by
  have hd := (hb L).1
  have hg : AnalyticAt ℂ (fun w => sgStar L (α * w)) z :=
    (by fun_prop : Differentiable ℂ fun w => sgStar L (α * w)).analyticAt z
  have e : num L α = (fun w => sgStar L (α * w)) * (fun w => sgStar L (α * w)) := by
    funext w; exact sq _
  rw [e, meromorphicOrderAt_mul hg.meromorphicAt hg.meromorphicAt]
  have := sg_order L hord he α 0 z hα
  simp only [add_zero] at this
  rw [this, add_self_eq_two_mul_extended_int]
end Formalism.L2.Th1.F.IsogenySigmaQuotient
