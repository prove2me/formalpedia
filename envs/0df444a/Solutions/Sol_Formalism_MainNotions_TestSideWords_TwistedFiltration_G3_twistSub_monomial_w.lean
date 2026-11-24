-- Prove2me | solution 1 for Formalism.MainNotions.TestSideWords.TwistedFiltration.G3.twistSub_monomial_w
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T11:08:34.94464+00:00
-- url     : https://prove2.me/submissions/1e31f321-822b-48b4-bfdd-6e9f9e8d57c9

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_TwistedSubstitution_TwistedMonomialFiltration_MaxTwistDegreePderivLeAddOne
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_TwistedSubstitution_TwistedMonomialFiltration_TwistSubXMemSupported
import Theorems.Thm_Formalism_MainNotions_TestSideWords_TwistedFiltration_G2_twistSub_X_out


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
open Formalism Formalism.MainNotions Formalism.MainNotions.TestSideWords Formalism.MainNotions.TestSideWords.TwistedFiltration Formalism.MainNotions.TestSideWords.TwistedFiltration.G3
open Formalism.MainNotions.G Formalism.MainNotions.TestSideWords.TwistedFiltration.G1
variable {R : Type*} [CommRing R] {ι : Type} {n : ℕ} [NeZero n] (LL : Letters ι) (S : Set ι)
open Classical
namespace Formalism.MainNotions.TestSideWords.TwistedFiltration.G3
theorem _root_.solution (w : Set ι) (hd : Disjoint S w) (j : Fin n) (M' : ι × Fin n →₀ ℕ)
    (hM' : M'.filter (fun v => v.1 ∉ w) = 0) :
    twistSub (R := R) LL S j (monomial M' 1) = monomial M' 1 := by
  rw [monomial_eq, map_mul, Finsupp.prod, map_prod, monomial_eq, Finsupp.prod]
  congr 1
  · rw [twistSub, eval₂Hom_C, map_one, map_one]
  · refine Finset.prod_congr rfl fun v hv => ?_
    rw [map_pow]
    congr 1
    have hw : v.1 ∈ w := by
      by_contra hw
      have : (M'.filter (fun v => v.1 ∉ w)) v = 0 := by rw [hM']; rfl
      rw [Finsupp.filter_apply, if_pos hw] at this
      exact (Finsupp.mem_support_iff.1 hv) this
    exact Formalism.MainNotions.TestSideWords.TwistedFiltration.G2.twistSub_X_out LL S j v (Set.disjoint_right.1 hd hw)
end Formalism.MainNotions.TestSideWords.TwistedFiltration.G3
