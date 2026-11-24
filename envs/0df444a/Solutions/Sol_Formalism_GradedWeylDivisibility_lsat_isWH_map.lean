-- Prove2me | solution 1 for Formalism.GradedWeylDivisibility.lsat_isWH_map
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:28:58.545255+00:00
-- url     : https://prove2.me/submissions/511a445f-801d-43d1-9afb-8082172a6b66

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementA
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LSatLemmas

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
open Formalism Formalism.GradedWeylDivisibility
namespace Formalism.GradedWeylDivisibility
theorem _root_.solution {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) {σ M : Type*}
    [AddCommMonoid M] (w : σ → M) (m : M) (f : MvPolynomial σ R)
    (hf : IsWeightedHomogeneous w f m) : IsWeightedHomogeneous w (map φ f) m := by
  intro d hd
  apply hf
  intro h0
  apply hd
  rw [coeff_map, h0, map_zero]
end Formalism.GradedWeylDivisibility
