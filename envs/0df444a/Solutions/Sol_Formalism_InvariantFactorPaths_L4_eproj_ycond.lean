-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.L4.eproj_ycond
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:06:00.81529+00:00
-- url     : https://prove2.me/submissions/5a98f98e-da56-42d0-8520-3e2d7769817d

import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_StatementC
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_ResInto
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_MulEarlyLettersHolds
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_RestrictionMinMaxIntHolds
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_eproj_typeProj
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_typeProj_range_le_ycond
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_ycond_fix


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
theorem _root_.solution [NeZero r] (LL : Letters N) (j' j : ℕ) (hjj : j' ≤ j) (ρ : Fin r) (w : Fin r → ℤ)
    (PE : MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p])
    (hPE : IsEProj p LL j ρ w PE) (Mt : WithTop ℤ)
    (P : MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p])
    (hP : IsTypeProj p LL j' univ {la | ((la 0 : ℤ) : WithTop ℤ) ≤ Mt} P) :
    ∀ h ∈ YCond p LL j' Mt ⊓ Pol p r LL, h ∈ WtSpC p LL j univ w → PE h ∈ YCond p LL j' Mt := by
  intro h hh hW
  have h1 : P h = h := ycond_fix LL j' _ Mt P hP (fun la hla => hla) h hh
  have h2 := eproj_typeProj LL j' j hjj ρ w PE hPE _ P hP h hW
  rw [h1] at h2
  rw [h2]
  exact typeProj_range_le_ycond LL j' _ Mt P hP (fun la hla => hla) _
end Formalism.InvariantFactorPaths.L4
