-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.PW.iSup_weylLat_div
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T09:58:51.641248+00:00
-- url     : https://prove2.me/submissions/e6bb9373-c7d8-425c-affa-7a16bde39ccd

import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_LatData
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_CommProjectionHolds
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_StatementB
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_ZpClosedToAddSubgroup
import Theorems.Thm_Formalism_InvariantFactorPaths_PW_weylLat_div

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
theorem _root_.solution (LL : Letters N) (j : ℕ) (Q : MvPolynomial (Fin N × Fin r) ℚ_[p] → Prop)
    (c d : Fin r) (hcd : c ≠ d) (k : ℕ) (x : MvPolynomial (Fin N × Fin r) ℚ_[p])
    (hx : x ∈ ⨆ (h : MvPolynomial (Fin N × Fin r) ℚ_[p]) (_ : Q h), WeylLat p LL j h) :
    (((k.factorial : ℚ_[p]))⁻¹) • ((glAct p LL j c d) ^ k) x ∈
      ⨆ (h : MvPolynomial (Fin N × Fin r) ℚ_[p]) (_ : Q h), WeylLat p LL j h := by
  have hle : (⨆ (h : MvPolynomial (Fin N × Fin r) ℚ_[p]) (_ : Q h), WeylLat p LL j h) ≤
      (⨆ (h : MvPolynomial (Fin N × Fin r) ℚ_[p]) (_ : Q h), WeylLat p LL j h).comap
        (((((k.factorial : ℚ_[p]))⁻¹) • ((glAct p LL j c d) ^ k) :
          MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p]).restrictScalars ℤ_[p]) := by
    refine iSup_le fun h => iSup_le fun hh => ?_
    intro y hy
    rw [Submodule.mem_comap]
    exact (le_iSup_of_le h (le_iSup_of_le hh le_rfl) :
      WeylLat p LL j h ≤ ⨆ (h : MvPolynomial (Fin N × Fin r) ℚ_[p]) (_ : Q h), WeylLat p LL j h)
      (weylLat_div LL j h c d hcd k y hy)
  exact hle hx
end Formalism.InvariantFactorPaths.PW
