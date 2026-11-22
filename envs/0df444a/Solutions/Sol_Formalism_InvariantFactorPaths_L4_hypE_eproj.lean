-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.L4.hypE_eproj
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:43:36.253798+00:00
-- url     : https://prove2.me/submissions/a17541a5-3d48-4e2a-aa02-ff1c50c36d79

import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_StatementC
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_ResInto
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_MulEarlyLettersHolds
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_RestrictionMinMaxIntHolds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.L4
open Formalism.GM Formalism.GM.M Formalism.GM.TM Formalism.GM.MeanGammaLemmas Formalism.CountingSumsFrames MvPolynomial Finset
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}
namespace Formalism.InvariantFactorPaths.L4
theorem _root_.solution (LL : Letters N) (ρ : Fin r) (e1 : ℕ) (hE : HypE p LL ρ e1) (j : ℕ) (hj : j ≤ N) (w : Fin r → ℤ) :
    ∃ PE, IsEProj p LL j ρ w PE ∧
      (∀ F G, F ∈ WtSpC p LL j univ w → G ∈ WtSpC p LL j univ w → fock p (PE F) G = fock p F (PE G)) ∧
      ∀ F ∈ PolZ p r LL, F ∈ WtSpC p LL j univ w → ((p : ℚ_[p]) ^ e1) • PE F ∈ IntPol p (Fin N × Fin r) := by
  obtain ⟨PE, h1, h2, h3, h4, h5⟩ := hE j hj w
  exact ⟨PE, ⟨h1, h2, h3⟩, h4, h5⟩
end Formalism.InvariantFactorPaths.L4
