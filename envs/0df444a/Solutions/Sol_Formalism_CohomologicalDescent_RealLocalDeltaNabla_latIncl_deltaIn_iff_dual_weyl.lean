-- Prove2me | solution 1 for Formalism.CohomologicalDescent.RealLocalDeltaNabla.latIncl_deltaIn_iff_dual_weyl
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:19:02.340862+00:00
-- url     : https://prove2.me/submissions/441c97a8-6586-4ee7-a50c-828ebeb990e9

import Definitions.Def_Formalism_PieriBlockIdeals_LocalFaithfullyFlat
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_SL2BinomialLattices
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_ExactExponentLatticeIncl
import Definitions.Def_Formalism_GradedWeylDivisibility_DualWeylDominanceOf
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_RealLocalDeltaNabla

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial TensorProduct
noncomputable section
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.RealLocalDeltaNabla
open Formalism.GradedWeylDivisibility Formalism.UG Formalism.RankGapBounds.JumpSetsAlt Formalism.RankGapBounds.FormsTensorLocalization Formalism.CohomologicalDescent.LA Formalism.CohomologicalDescent.SL2BinomialLattices
namespace Formalism.CohomologicalDescent.RealLocalDeltaNabla
theorem _root_.solution (O : Type) [CommRing O] (r n : ℕ) (hn : n ≤ r) (ν : Fin n → ℕ) (t : O)
    (e : ℕ) : LatIncl t (deltaIn O r n hn ν) e ↔
      ∀ x ∈ dualWeyl O r n ν, t ^ e • x ∈ weyl O r n hn ν := by
  unfold LatIncl
  exact ⟨fun h x hx => h ⟨x, hx⟩, fun h x => h x.1 x.2⟩
end Formalism.CohomologicalDescent.RealLocalDeltaNabla
