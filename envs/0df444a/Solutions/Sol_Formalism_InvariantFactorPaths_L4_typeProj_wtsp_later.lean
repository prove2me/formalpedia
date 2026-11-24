-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.L4.typeProj_wtsp_later
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T10:22:00.242873+00:00
-- url     : https://prove2.me/submissions/ac442580-c29a-49c3-ac83-5c30b4a813fa

import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_StatementC
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_ResInto
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_MulEarlyLettersHolds
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_RestrictionMinMaxIntHolds
import Theorems.Thm_Formalism_CountingSumsFrames_comm_wtsp
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_typeProj_comm_later


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
theorem _root_.solution (LL : Letters N) (j' j : ℕ) (hjj : j' ≤ j) (T : Set (Fin r → ℤ))
    (P : MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p])
    (hP : IsTypeProj p LL j' univ T P) (w : Fin r → ℤ) :
    ∀ x ∈ WtSpC p LL j univ w, P x ∈ WtSpC p LL j univ w :=
  comm_wtsp LL j P (fun c x => typeProj_comm_later LL j' j hjj T P hP c c x) w
end Formalism.InvariantFactorPaths.L4
