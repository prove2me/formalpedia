-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.fact_eq_prod
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:53:16.026977+00:00
-- url     : https://prove2.me/submissions/841cdbc2-effa-4fda-8abd-ff5edfd928aa

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_MemPolKIff
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_CgeZeroIffIntegral

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
theorem _root_.solution {σ : Type} [Fintype σ] (α : σ →₀ ℕ) : fact α = ∏ x, (α x).factorial := by
  unfold fact
  exact Finsupp.prod_fintype _ _ (fun _ => Nat.factorial_zero)
end Formalism.MainNotions.PlaneGram
