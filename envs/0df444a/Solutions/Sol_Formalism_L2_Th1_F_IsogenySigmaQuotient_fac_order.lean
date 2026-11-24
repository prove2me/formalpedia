-- Prove2me | solution 1 for Formalism.L2.Th1.F.IsogenySigmaQuotient.fac_order
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T10:37:41.313289+00:00
-- url     : https://prove2.me/submissions/0ad9f210-0939-48ae-8b15-61884492ce91

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_TranslateProduct
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_IsogenySigma
import Theorems.Thm_Formalism_L2_Th1_F_IsogenySigmaQuotient_sg_add_order
import Theorems.Thm_Formalism_L2_Th1_F_IsogenySigmaQuotient_sg_sub_order
import Theorems.Thm_Formalism_L2_Th1_F_IsogenySigmaQuotient_sg_add_analyticAt
import Theorems.Thm_Formalism_L2_Th1_F_IsogenySigmaQuotient_sg_sub_analyticAt
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
private lemma meromorphicOrderAt_eq_zero_of_analyticAt_ne_zero {g : ℂ → ℂ} {x : ℂ} (hg : AnalyticAt ℂ g x) (h : g x ≠ 0) :
    meromorphicOrderAt g x = 0 := by
  have := (meromorphicOrderAt_eq_int_iff (n := 0) hg.meromorphicAt).2 ⟨g, hg, h, by simp⟩
  simpa using this
variable (α : ℂ) (S : Finset ℂ)
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
theorem _root_.solution (hord : SigmaOrder) (he : SigmaEntire) (hb : SgStarBasic) (P z : ℂ)
    (hP : P ∉ L.lattice) :
    meromorphicOrderAt (fac L P) z = ind L (z + P) + ind L (z - P) := by
  have hs : sgStar L P ≠ 0 := fun h => hP (((hb L).2.2.1 P).1 h)
  have h0 : AnalyticAt ℂ (fun _ : ℂ => -(sgStar L P ^ 2)⁻¹) z := analyticAt_const
  have h1 := sg_add_analyticAt L hb P z
  have h2 := sg_sub_analyticAt L hb P z
  have h12 : AnalyticAt ℂ ((fun w => sgStar L (w + P)) * fun w => sgStar L (w - P)) z := h1.mul h2
  have e : fac L P = (fun _ : ℂ => -(sgStar L P ^ 2)⁻¹) *
      ((fun w => sgStar L (w + P)) * fun w => sgStar L (w - P)) := by
    funext w; rfl
  rw [e, meromorphicOrderAt_mul h0.meromorphicAt h12.meromorphicAt,
    meromorphicOrderAt_mul h1.meromorphicAt h2.meromorphicAt,
    meromorphicOrderAt_eq_zero_of_analyticAt_ne_zero h0 (by simp [hs]), sg_add_order L hord he P z, sg_sub_order L hord he P z, zero_add]
end Formalism.L2.Th1.F.IsogenySigmaQuotient
