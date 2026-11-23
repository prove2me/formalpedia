-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.fact_add_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:57:32.82636+00:00
-- url     : https://prove2.me/submissions/63213e41-62c0-4eef-bad5-b05f19fa91f9

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_MemPolKIff
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_CgeZeroIffIntegral
import Theorems.Thm_Formalism_MainNotions_PlaneGram_fact_eq_prod

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Finset
open Formalism Formalism.MainNotions Formalism.MainNotions.PlaneGram
variable {K : Type} [Field K] (v : AddValuation K (WithTop ℚ))
namespace Formalism.MainNotions.PlaneGram
theorem _root_.solution {σ : Type} [Fintype σ] (α α' : σ →₀ ℕ) :
    fact (α + α') = (∏ x, (α x + α' x).choose (α' x)) * fact α * fact α' := by
  rw [fact_eq_prod, fact_eq_prod, fact_eq_prod, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun x _ => ?_
  rw [Finsupp.add_apply, Nat.add_choose_mul_factorial_mul_factorial]
end Formalism.MainNotions.PlaneGram
