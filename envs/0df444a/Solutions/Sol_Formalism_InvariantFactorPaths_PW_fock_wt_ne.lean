-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.PW.fock_wt_ne
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T01:09:46.649844+00:00
-- url     : https://prove2.me/submissions/eeb52556-8a5d-440e-8ae4-aae7909f5f97

import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_WeightCompApply
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_FischerAdjointnessHolds
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_OrthogonalIsomorphismHolds
import Theorems.Thm_Formalism_InvariantFactorPaths_PW_GAe_isWt_iff
import Theorems.Thm_Formalism_InvariantFactorPaths_PW_fock_disjoint


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
variable {p : ℕ} [Fact p.Prime] {N r n : ℕ}
namespace Formalism.InvariantFactorPaths.PW
theorem _root_.solution (LL : Letters N) (j : ℕ) (e : Fin n ↪o Fin r) {μ ν : Fin n → ℤ} (hne : μ ≠ ν)
    {x y : MvPolynomial (Fin N × Fin r) ℚ_[p]} (hx : (GAe p LL j e).IsWt μ x) (hy : (GAe p LL j e).IsWt ν y) :
    fock p x y = 0 := by
  rw [GAe_isWt_iff, MvPolynomial.mem_restrictSupport_iff] at hx hy
  apply fock_disjoint
  intro m hmx hmy
  obtain ⟨a, ha⟩ := Function.ne_iff.mp hne
  have h1 : wt LL j (e a) m = μ a := hx hmx a
  have h2 : wt LL j (e a) m = ν a := hy hmy a
  exact ha (h1.symm.trans h2)
end Formalism.InvariantFactorPaths.PW
