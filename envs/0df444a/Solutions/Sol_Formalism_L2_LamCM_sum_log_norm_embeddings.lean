-- Prove2me | solution 1 for Formalism.L2.LamCM.sum_log_norm_embeddings
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:08:01.013921+00:00
-- url     : https://prove2.me/submissions/769e525c-077c-4ff0-8b08-2ed98b990aca

import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_StatementA
import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_StatementB
import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_CMIdealValuations_ValuationLeOfEqAlgebraMap

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.LamCM
open NumberField IsDedekindDomain MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped nonZeroDivisors ComplexOrder
variable {K : Type} [Field K] [NumberField K]
namespace Formalism.L2.LamCM
theorem _root_.solution {k : K} (hk : k ≠ 0) :
    ∑ σ : K →+* ℂ, Real.log ‖σ k‖ =
      Real.log ((FractionalIdeal.absNorm (FractionalIdeal.spanSingleton (𝓞 K)⁰ k) : ℚ) : ℝ) := by
  have e : ∏ σ : K →+* ℂ, σ k = algebraMap ℚ ℂ (Algebra.norm ℚ k) := by
    rw [Algebra.norm_eq_prod_embeddings ℚ ℂ]
    exact Fintype.prod_equiv (RingHom.equivRatAlgHom K ℂ) _ _ (fun σ => rfl)
  rw [← Real.log_prod (fun σ _ => norm_ne_zero_iff.mpr ((map_ne_zero σ).mpr hk)), ← norm_prod, e,
    FractionalIdeal.absNorm_span_singleton]
  simp
end Formalism.L2.LamCM
