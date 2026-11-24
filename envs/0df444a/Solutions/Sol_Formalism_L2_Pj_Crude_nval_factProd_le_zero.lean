-- Prove2me | solution 1 for Formalism.L2.Pj.Crude.nval_factProd_le_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:28:16.067413+00:00
-- url     : https://prove2.me/submissions/a637e7c6-594f-45cd-83e4-358b7badb1a9

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_PlaceBelow
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CrudeVal
import Theorems.Thm_Formalism_L2_Pj_Crude_resCharOf_prime
import Theorems.Thm_Formalism_L2_Pj_Crude_crv_nval_natCast
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
theorem _root_.solution (ho : OverLa la V ι e) {σ : Type} (α : σ →₀ ℕ) (hα : ∀ s, α s < resCharOf la) :
    nval V e (((α.prod fun _ t => t.factorial : ℕ) : K')) ≤ 0 := by
  have hp := resCharOf_prime la
  haveI : Fact (resCharOf la).Prime := ⟨hp⟩
  have hne : (α.prod fun _ t => t.factorial) ≠ 0 := by
    simp only [Finsupp.prod]
    exact Finset.prod_ne_zero_iff.mpr fun _ _ => Nat.factorial_ne_zero _
  have hv : padicValNat (resCharOf la) (α.prod fun _ t => t.factorial) = 0 := by
    rw [crv_padic_prod]
    refine Finset.sum_eq_zero fun s _ => padicValNat.eq_zero_of_not_dvd ?_
    rw [hp.dvd_factorial]
    exact not_le.mpr (hα s)
  rw [crv_nval_natCast la ho hne, hv]
  simp
end Formalism.L2.Pj.Crude
