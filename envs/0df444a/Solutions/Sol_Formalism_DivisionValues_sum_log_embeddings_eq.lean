-- Prove2me | solution 1 for Formalism.DivisionValues.sum_log_embeddings_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:27:18.221839+00:00
-- url     : https://prove2.me/submissions/80c65abd-f99a-4853-85b2-ac71cac86bb2

import Definitions.Def_Formalism_QuotientMetricDivisors_ProdFormula
import Definitions.Def_Formalism_LogFactorialIndices_SignedSubspaceIndex_LogProductFormula
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ProdFormula

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
noncomputable section
open Formalism Formalism.DivisionValues
namespace Formalism.DivisionValues
theorem _root_.solution (K : Type) [Field K] [NumberField K] (a : K) (ha : a ≠ 0) :
    ∑ σ : K →+* ℂ, Real.log ‖σ a‖ = Real.log |((Algebra.norm ℚ a : ℚ) : ℝ)| := by
  have h := Algebra.norm_eq_prod_embeddings ℚ ℂ a
  have hq : (algebraMap ℚ ℂ) (Algebra.norm ℚ a) = ((Algebra.norm ℚ a : ℚ) : ℂ) := eq_ratCast _ _
  have hprod : ((Algebra.norm ℚ a : ℚ) : ℂ) = ∏ σ : K →+* ℂ, σ a := by
    rw [← hq, h]
    exact Fintype.prod_equiv (RingHom.equivRatAlgHom K ℂ).symm _ _ (fun _ => rfl)
  have hn : |((Algebra.norm ℚ a : ℚ) : ℝ)| = ∏ σ : K →+* ℂ, ‖σ a‖ := by
    rw [← norm_prod, ← hprod]
    simp
  rw [hn, Real.log_prod (fun σ _ => by simpa using ha)]
end Formalism.DivisionValues
