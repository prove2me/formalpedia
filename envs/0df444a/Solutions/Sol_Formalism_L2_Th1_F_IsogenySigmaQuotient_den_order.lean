-- Prove2me | solution 1 for Formalism.L2.Th1.F.IsogenySigmaQuotient.den_order
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T10:53:00.748949+00:00
-- url     : https://prove2.me/submissions/c18739d6-deac-4453-b548-9c6947055d01

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_TranslateProduct
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_IsogenySigma
import Theorems.Thm_Formalism_L2_Th1_F_IsogenySigmaQuotient_fac_analyticAt
import Theorems.Thm_Formalism_L2_Th1_F_IsogenySigmaQuotient_fac_order
import Theorems.Thm_Formalism_L2_Th1_F_IsogenySigmaQuotient_sg_id_order
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
private lemma analyticAt_prod_fac (hb : SgStarBasic) (T : Finset ℂ) (z : ℂ) :
    AnalyticAt ℂ (fun w => ∏ P ∈ T, fac L P w) z := by
  refine Finset.induction_on T ?_ ?_
  · simp only [Finset.prod_empty]; exact analyticAt_const
  · intro a T ha ih
    have e : (fun w => ∏ P ∈ insert a T, fac L P w) = fun w => fac L a w * ∏ P ∈ T, fac L P w := by
      funext w; rw [Finset.prod_insert ha]
    rw [e]; exact (fac_analyticAt L hb a z).mul ih
private lemma add_self_eq_two_mul_extended_int (x : WithTop ℤ) : x + x = 2 * x := by
  cases x with
  | top => first | rfl | decide | simp
  | coe a =>
    rw [← WithTop.coe_add, show (2 : WithTop ℤ) = ((2 : ℤ) : WithTop ℤ) from rfl, ← WithTop.coe_mul,
      two_mul]
private lemma meromorphicOrderAt_prod_fac (hord : SigmaOrder) (he : SigmaEntire) (hb : SgStarBasic)
    (T : Finset ℂ) (hT : ∀ P ∈ T, P ∉ L.lattice) (z : ℂ) :
    meromorphicOrderAt (fun w => ∏ P ∈ T, fac L P w) z = ∑ P ∈ T, (ind L (z + P) + ind L (z - P)) := by
  revert hT
  refine Finset.induction_on T ?_ ?_
  · intro _
    simp only [Finset.prod_empty, Finset.sum_empty]
    exact meromorphicOrderAt_eq_zero_of_analyticAt_ne_zero analyticAt_const one_ne_zero
  · intro a T ha ih hT
    have e : (fun w => ∏ P ∈ insert a T, fac L P w) = (fac L a) * fun w => ∏ P ∈ T, fac L P w := by
      funext w; rw [Finset.prod_insert ha]; rfl
    rw [e, meromorphicOrderAt_mul (fac_analyticAt L hb a z).meromorphicAt
      (analyticAt_prod_fac L hb T z).meromorphicAt,
      fac_order L hord he hb a z (hT a (Finset.mem_insert_self a T)),
      ih (fun P hP => hT P (Finset.mem_insert_of_mem hP)), Finset.sum_insert ha]
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
    (hS : ∀ P ∈ S, P ∉ L.lattice) (z : ℂ) :
    meromorphicOrderAt (den L α S) z
      = 2 * ind L z + ∑ P ∈ S, (ind L (z + P) + ind L (z - P)) := by
  have hd := (hb L).1
  have h1 : AnalyticAt ℂ (fun _ : ℂ => α ^ 2) z := analyticAt_const
  have h2 : AnalyticAt ℂ (fun w => sgStar L w ^ 2) z :=
    (by fun_prop : Differentiable ℂ fun w => sgStar L w ^ 2).analyticAt z
  have h12 : AnalyticAt ℂ ((fun _ : ℂ => α ^ 2) * fun w => sgStar L w ^ 2) z := h1.mul h2
  have e : den L α S = ((fun _ : ℂ => α ^ 2) * fun w => sgStar L w ^ 2) * fun w => ∏ P ∈ S, fac L P w := by
    funext w; rfl
  have hs : (fun w => sgStar L w ^ 2) = sgStar L * sgStar L := by
    funext w; exact sq _
  have hm : MeromorphicAt (sgStar L) z := (hd.analyticAt z).meromorphicAt
  rw [e, meromorphicOrderAt_mul h12.meromorphicAt (analyticAt_prod_fac L hb S z).meromorphicAt,
    meromorphicOrderAt_mul h1.meromorphicAt h2.meromorphicAt, meromorphicOrderAt_eq_zero_of_analyticAt_ne_zero h1 (pow_ne_zero 2 hα),
    meromorphicOrderAt_prod_fac L hord he hb S hS z, zero_add, hs, meromorphicOrderAt_mul hm hm,
    sg_id_order L hord he z, add_self_eq_two_mul_extended_int]
end Formalism.L2.Th1.F.IsogenySigmaQuotient
