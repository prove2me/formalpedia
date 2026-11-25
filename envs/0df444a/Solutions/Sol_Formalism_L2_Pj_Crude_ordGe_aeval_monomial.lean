-- Prove2me | solution 1 for Formalism.L2.Pj.Crude.ordGe_aeval_monomial
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:11:52.035975+00:00
-- url     : https://prove2.me/submissions/1e9701ba-160d-458a-ac88-5b2a45a87d11

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CrudeBase
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CrudeDiv
import Theorems.Thm_Formalism_L2_Pj_Crude_div_ordGe_mul
import Theorems.Thm_Formalism_L2_Pj_Crude_div_ordGe_one
import Theorems.Thm_Formalism_L2_Pj_Crude_div_ordGe_pow

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
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
variable {k : Type} [CommRing k] {d n : ℕ}
namespace Formalism.L2.Pj.Crude
theorem _root_.solution {ι : Type} (φ : ι → PS k n d) (hφ : ∀ i, OrdGe 1 (φ i)) (α : ι →₀ ℕ) :
    OrdGe α.degree (MvPolynomial.aeval φ (MvPolynomial.monomial α (1 : k))) := by
  classical
  have key : ∀ s : Finset ι, OrdGe (∑ i ∈ s, α i) (∏ i ∈ s, φ i ^ α i) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa using div_ordGe_one
    | insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.prod_insert hi]
      have h := div_ordGe_pow (hφ i) (α i)
      rw [one_mul] at h
      exact div_ordGe_mul h ih
  rw [MvPolynomial.aeval_monomial, map_one, one_mul]
  exact key α.support
end Formalism.L2.Pj.Crude
