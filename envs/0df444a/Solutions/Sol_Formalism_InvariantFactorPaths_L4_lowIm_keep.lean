-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.L4.lowIm_keep
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:49:30.258786+00:00
-- url     : https://prove2.me/submissions/2f2cd369-2e43-44a2-b22c-405a4b164f56

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
theorem _root_.solution (LL : Letters N) (j : ℕ) (ρ : Fin r)
    (Q : MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p])
    (hQ : ∀ c ∈ univ.erase ρ, ∀ d ∈ univ.erase ρ, ∀ x, Q (glAct p LL j c d x) = glAct p LL j c d (Q x)) :
    ∀ x ∈ LowIm p LL j ρ, Q x ∈ LowIm p LL j ρ := by
  intro x hx
  have key : LowIm p LL j ρ ≤ (LowIm p LL j ρ).comap Q := by
    unfold LowIm
    refine iSup_le fun c => iSup_le fun d => iSup_le fun h => ?_
    intro y hy
    obtain ⟨z, -, rfl⟩ := Submodule.mem_map.mp hy
    rw [Submodule.mem_comap, hQ c h.1 d h.2.1 z]
    exact Submodule.mem_iSup_of_mem c (Submodule.mem_iSup_of_mem d
      (Submodule.mem_iSup_of_mem h (Submodule.mem_map_of_mem Submodule.mem_top)))
  exact key hx
end Formalism.InvariantFactorPaths.L4
