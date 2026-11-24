-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.L4.mem_typesLE_of_ycondC
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T10:49:39.084355+00:00
-- url     : https://prove2.me/submissions/b0730e0c-f5b8-44e6-bd05-b91b867c45d1

import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_InitPartZeroXMul
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_FirstWeightLeOfSupport
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
theorem _root_.solution [NeZero r] (LL : Letters N) (j : ℕ) (Cs : Finset (Fin r)) (h0 : (0 : Fin r) ∈ Cs)
    (Mt : WithTop ℤ)
    (P : MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p])
    (hP : IsTypeProj p LL j Cs {la | ((la 0 : ℤ) : WithTop ℤ) ≤ Mt} P) :
    ∀ x ∈ YCondC p LL j Cs Mt ⊓ Pol p r LL, x ∈ TypesLE p LL j Cs Mt := by
  intro x hx
  have hfix := ycondC_fix LL j Cs h0 Mt _ P hP (fun la h => h) x hx
  have h1 : x ∈ LinearMap.range P := ⟨x, hfix⟩
  rw [hP.2.1] at h1
  exact h1
end Formalism.InvariantFactorPaths.L4
