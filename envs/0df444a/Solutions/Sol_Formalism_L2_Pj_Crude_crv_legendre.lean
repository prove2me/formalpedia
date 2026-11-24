-- Prove2me | solution 1 for Formalism.L2.Pj.Crude.crv_legendre
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T10:14:40.525795+00:00
-- url     : https://prove2.me/submissions/4b155e0a-23a6-455e-9c7c-49234bbd5da4

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_PlaceBelow
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CrudeVal
import Theorems.Thm_Formalism_L2_Pj_Crude_crv_padic_prod

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
    (p - 1) * padicValNat p (α.prod fun _ t => t.factorial) ≤ α.degree := by
  rw [crv_padic_prod, Finset.mul_sum]
  unfold Finsupp.degree
  exact Finset.sum_le_sum fun s _ => by
    rw [sub_one_mul_padicValNat_factorial]
    exact Nat.sub_le _ _
end Formalism.L2.Pj.Crude
