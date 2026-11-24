-- Prove2me | solution 1 for Formalism.GradedWeylDivisibility.ldlat_isWH_map
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:34:09.518494+00:00
-- url     : https://prove2.me/submissions/b1712621-f594-4db2-aa3f-419973d5fa7a

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementD
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LDlatLemmas

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
    [AddCommMonoid M] {w : σ → M} {f : MvPolynomial σ R} {μ : M}
    (hf : IsWeightedHomogeneous w f μ) : IsWeightedHomogeneous w (map φ f) μ := by
  intro m hm
  apply hf
  intro h0
  apply hm
  rw [coeff_map, h0, map_zero]
end Formalism.GradedWeylDivisibility
