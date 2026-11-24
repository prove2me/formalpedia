-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.L4.eproj_typeProj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T10:35:22.306639+00:00
-- url     : https://prove2.me/submissions/4c86924b-2aed-4917-864b-e2b3e8c3516c

import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_StatementC
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_ResInto
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_MulEarlyLettersHolds
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_RestrictionMinMaxIntHolds
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_eproj_comm
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_typeProj_wtsp_later
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
theorem _root_.solution (LL : Letters N) (j' j : ℕ) (hjj : j' ≤ j) (ρ : Fin r) (w : Fin r → ℤ)
    (PE : MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p])
    (hPE : IsEProj p LL j ρ w PE) (T : Set (Fin r → ℤ))
    (P : MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p])
    (hP : IsTypeProj p LL j' univ T P) :
    ∀ F ∈ WtSpC p LL j univ w, PE (P F) = P (PE F) :=
  eproj_comm LL j ρ w w PE PE hPE hPE P
    (fun c _ d _ x => typeProj_comm_later LL j' j hjj T P hP c d x) (typeProj_wtsp_later LL j' j hjj T P hP w)
end Formalism.InvariantFactorPaths.L4
