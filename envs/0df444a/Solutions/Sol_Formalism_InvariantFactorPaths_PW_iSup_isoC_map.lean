-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.PW.iSup_isoC_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T09:50:24.046487+00:00
-- url     : https://prove2.me/submissions/e454b008-ce05-46ad-9ceb-4335d08bf543

import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_WeightCompApply
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_StatementC
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_CommProjectionHolds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.PW
open Formalism.GM.M Formalism.GM.DimensionMonotonicity MvPolynomial Finset
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}
namespace Formalism.InvariantFactorPaths.PW
theorem _root_.solution (LL : Letters N) (j : ℕ) (Cs : Finset (Fin r)) (Q : (Fin r → ℤ) → Prop)
    (A : MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p])
    (hA : ∀ la, ∀ x ∈ IsoC p LL j Cs la, A x ∈ IsoC p LL j Cs la) :
    ∀ x ∈ (⨆ (la : Fin r → ℤ) (_ : Q la), IsoC p LL j Cs la),
      A x ∈ (⨆ (la : Fin r → ℤ) (_ : Q la), IsoC p LL j Cs la) := by
  have hle : (⨆ (la : Fin r → ℤ) (_ : Q la), IsoC p LL j Cs la) ≤
      (⨆ (la : Fin r → ℤ) (_ : Q la), IsoC p LL j Cs la).comap A := by
    refine iSup_le fun la => iSup_le fun hla => ?_
    intro x hx
    rw [Submodule.mem_comap]
    exact (le_iSup_of_le la (le_iSup_of_le hla le_rfl) :
      IsoC p LL j Cs la ≤ ⨆ (la : Fin r → ℤ) (_ : Q la), IsoC p LL j Cs la) (hA la x hx)
  exact fun x hx => hle hx
end Formalism.InvariantFactorPaths.PW
