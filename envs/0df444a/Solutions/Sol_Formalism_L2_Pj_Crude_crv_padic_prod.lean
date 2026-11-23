-- Prove2me | solution 1 for Formalism.L2.Pj.Crude.crv_padic_prod
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:43:43.598814+00:00
-- url     : https://prove2.me/submissions/773f6664-d52e-4d2b-b7bf-416e548177fa

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_PlaceBelow
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CrudeVal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Pj Formalism.L2.Pj.Crude
open NumberField IsDedekindDomain Formalism.L2.Pj
open scoped WithZero
variable {K : Type} [Field K] [NumberField K] (la : HeightOneSpectrum (𝓞 K))
  {V K' : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K'] [Algebra V K']
  [IsFractionRing V K'] {ι : K →+* K'} {e : ℕ}
namespace Formalism.L2.Pj.Crude
theorem _root_.solution {σ : Type} (p : ℕ) [Fact p.Prime] (α : σ →₀ ℕ) :
    padicValNat p (α.prod fun _ t => t.factorial) = ∑ s ∈ α.support, padicValNat p (α s).factorial := by
  classical
  simp only [Finsupp.prod]
  refine Finset.induction_on α.support ?_ ?_
  · simp
  · intro a u ha ih
    rw [Finset.prod_insert ha, Finset.sum_insert ha,
      padicValNat.mul (Nat.factorial_ne_zero _)
        (Finset.prod_ne_zero_iff.mpr fun _ _ => Nat.factorial_ne_zero _), ih]
end Formalism.L2.Pj.Crude
