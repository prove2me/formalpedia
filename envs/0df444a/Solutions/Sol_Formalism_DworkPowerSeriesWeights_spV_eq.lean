-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.spV_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:08:46.999239+00:00
-- url     : https://prove2.me/submissions/c5179a55-535e-416a-ac8a-3598574741ea

import Definitions.Def_Formalism_GaussJetBounds_GenLogInverse
import Definitions.Def_Formalism_GaussJetBounds_StatementB
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_Special

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
universe u v
open Formalism Formalism.DworkPowerSeriesWeights
open Formalism.IncomingBounds
variable {R : Type*} [CommRing R] {m p : ℕ}
namespace Formalism.DworkPowerSeriesWeights
theorem _root_.solution (top : Fin (p + 1) → R) (o : Option (Fin m)) (c : Fin (p + 1)) :
    spV top o c = MvPolynomial.monomial (spEx o c) (spCo top o c) := by
  cases o
  · show MvPolynomial.C (top c) = MvPolynomial.monomial 0 (top c)
    exact MvPolynomial.C_apply
  · simp [spV, spEx, spCo, MvPolynomial.X]
end Formalism.DworkPowerSeriesWeights
