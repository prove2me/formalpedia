-- Prove2me | solution 1 for Formalism.L2.Th1.F.IsogenySigmaQuotient.sg_order
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:58:18.270604+00:00
-- url     : https://prove2.me/submissions/dd48f45e-86c3-4b50-91db-16d8c0834e42

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_TranslateProduct
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_IsogenySigma
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
namespace Formalism.L2.Th1.F.IsogenySigmaQuotient
theorem _root_.solution (hord : SigmaOrder) (he : SigmaEntire) (a b z : ℂ) (ha : a ≠ 0) :
    meromorphicOrderAt (fun w : ℂ => sgStar L (a * w + b)) z = ind L (a * z + b) := by
  have hA : AnalyticAt ℂ (fun w : ℂ => wSigma L (a * w + b)) z := by
    have hd := he L
    exact (by fun_prop : Differentiable ℂ fun w : ℂ => wSigma L (a * w + b)).analyticAt z
  have hE : AnalyticAt ℂ (fun w : ℂ => Complex.exp (-(s2 L) * (a * w + b) ^ 2 / 2)) z :=
    (by fun_prop : Differentiable ℂ fun w : ℂ => Complex.exp (-(s2 L) * (a * w + b) ^ 2 / 2)).analyticAt z
  have hf : (fun w : ℂ => sgStar L (a * w + b)) =
      (fun w : ℂ => wSigma L (a * w + b)) * fun w : ℂ => Complex.exp (-(s2 L) * (a * w + b) ^ 2 / 2) := by
    funext w; rfl
  rw [hf, meromorphicOrderAt_mul hA.meromorphicAt hE.meromorphicAt, hord L a b z ha,
    meromorphicOrderAt_eq_zero_of_analyticAt_ne_zero hE (Complex.exp_ne_zero _), add_zero]
  rfl
end Formalism.L2.Th1.F.IsogenySigmaQuotient
