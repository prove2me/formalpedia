-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.L4.ycond_fix
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T10:49:41.314882+00:00
-- url     : https://prove2.me/submissions/17f721c8-15e9-40f3-be4a-b4e4847beb81

import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_InitPartZeroXMul
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_FirstWeightLeOfSupport
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_ycond_le_ycondC
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_ycondC_fix

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.L4
open Formalism.GM Formalism.GM.M Formalism.GM.TM Formalism.CountingSumsFrames MvPolynomial Finset
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}
namespace Formalism.InvariantFactorPaths.L4
theorem _root_.solution [NeZero r] (LL : Letters N) (j : ℕ) (T : Set (Fin r → ℤ)) (Mt : WithTop ℤ)
    (P : MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p])
    (hP : IsTypeProj p LL j univ T P) (hT : ∀ la : Fin r → ℤ, ((la 0 : ℤ) : WithTop ℤ) ≤ Mt → la ∈ T) :
    ∀ x ∈ YCond p LL j Mt ⊓ Pol p r LL, P x = x := by
  intro x hx
  rw [Submodule.mem_inf] at hx
  exact ycondC_fix LL j univ (Finset.mem_univ _) Mt T P hP hT x
    (Submodule.mem_inf.mpr ⟨ycond_le_ycondC LL j univ Mt hx.1, hx.2⟩)
end Formalism.InvariantFactorPaths.L4
