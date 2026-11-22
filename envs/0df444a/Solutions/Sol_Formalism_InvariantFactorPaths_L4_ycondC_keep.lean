-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.L4.ycondC_keep
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:48:37.172186+00:00
-- url     : https://prove2.me/submissions/f088053c-50a4-4154-977c-089123796dd3

import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_InitPartZeroXMul
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_FirstWeightLeOfSupport
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_ycondC_glStable
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_ycondC_le_supp
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_le_ycondC

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
theorem _root_.solution [NeZero r] (LL : Letters N) (j : ℕ) (Cs : Finset (Fin r)) (Mt : WithTop ℤ)
    (Q : MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p])
    (hc : ∀ c ∈ Cs, ∀ d ∈ Cs, ∀ x, Q (glAct p LL j c d x) = glAct p LL j c d (Q x))
    (hw : ∀ x ∈ restrictSupport ℚ_[p] {m : Fin N × Fin r →₀ ℕ | ((wt LL j 0 m : ℤ) : WithTop ℤ) ≤ Mt},
      Q x ∈ restrictSupport ℚ_[p] {m : Fin N × Fin r →₀ ℕ | ((wt LL j 0 m : ℤ) : WithTop ℤ) ≤ Mt}) :
    ∀ x ∈ YCondC p LL j Cs Mt, Q x ∈ YCondC p LL j Cs Mt := by
  intro x hx
  have hle : (YCondC p LL j Cs Mt).map Q ≤ YCondC p LL j Cs Mt := by
    apply le_ycondC
    · rintro _ ⟨y, hy, rfl⟩
      exact hw y (ycondC_le_supp LL j Cs Mt hy)
    · rintro c hc1 d hd1 _ ⟨y, hy, rfl⟩
      exact ⟨glAct p LL j c d y, ycondC_glStable LL j Cs Mt c hc1 d hd1 y hy, hc c hc1 d hd1 y⟩
  exact hle ⟨x, hx, rfl⟩
end Formalism.InvariantFactorPaths.L4
