-- Prove2me | solution 1 for Formalism.L2.Th1.F.IsogenySigmaQuotient.quot_order
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T11:28:49.318911+00:00
-- url     : https://prove2.me/submissions/acba040b-66ca-4de9-bd81-c3eb9d1b12d4

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_TranslateProduct
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_IsogenySigma
import Theorems.Thm_Formalism_L2_Th1_F_IsogenySigmaQuotient_ind_of_mem
import Theorems.Thm_Formalism_L2_Th1_F_IsogenySigmaQuotient_ind_of_notMem
import Theorems.Thm_Formalism_L2_Th1_F_IsogenySigmaQuotient_num_analyticAt
import Theorems.Thm_Formalism_L2_Th1_F_IsogenySigmaQuotient_den_analyticAt
import Theorems.Thm_Formalism_L2_Th1_F_IsogenySigmaQuotient_num_order
import Theorems.Thm_Formalism_L2_Th1_F_IsogenySigmaQuotient_den_order_two
import Theorems.Thm_Formalism_L2_Th1_F_IsogenySigmaQuotient_mem_of_den_eq_zero
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
theorem _root_.solution (hord : SigmaOrder) (he : SigmaEntire) (hb : SgStarBasic) (hα : α ≠ 0)
    (hst : MulStable L α) (hS : IsKerReps L α S) (z : ℂ) :
    0 ≤ meromorphicOrderAt (fun w => num L α w / den L α S w) z := by
  have hnum := num_analyticAt L α hb z
  have hden := den_analyticAt L α S hb z
  have e : (fun w => num L α w / den L α S w) = num L α * (den L α S)⁻¹ := by
    funext w; exact div_eq_mul_inv _ _
  rw [e, meromorphicOrderAt_mul hnum.meromorphicAt hden.meromorphicAt.inv, meromorphicOrderAt_inv,
    num_order L α hord he hb hα z]
  by_cases h : α * z ∈ L.lattice
  · rw [den_order_two L α S hord he hb hα hS z h, ind_of_mem L h]
    decide
  · rw [meromorphicOrderAt_eq_zero_of_analyticAt_ne_zero hden (fun h0 => h (mem_of_den_eq_zero L α S hb hα hst hS z h0)), ind_of_notMem L h]
    decide
end Formalism.L2.Th1.F.IsogenySigmaQuotient
