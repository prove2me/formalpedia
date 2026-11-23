-- Prove2me | solution 1 for Formalism.QuantumDeterminants.BesselUnipotentEquiv.psi_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:11:02.620507+00:00
-- url     : https://prove2.me/submissions/954cd4bb-18d9-4f9c-97c2-2872d8a9cd2e

import Definitions.Def_Formalism_FormalDegreeBessel_StatementBF
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_BesselUnipotentEquivHolds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory
noncomputable section
open Formalism Formalism.QuantumDeterminants
open Formalism.QuantumDeterminants.BesselUnipotentEquiv
variable {k r : ℕ}
namespace Formalism.QuantumDeterminants.BesselUnipotentEquiv
theorem _root_.solution (z : Fin (2 * r + k + 1) → ℂ) (c : ℂ) (hz : inWb k r z) :
    psi k r z c 1 = 1 := by
  have h : ell k r z 1 = 0 := by
    unfold ell
    apply Finset.sum_eq_zero
    intro a _
    split_ifs with h'
    · rw [Matrix.one_apply_ne]
      intro he
      have := congrArg Fin.val he
      simp [eI] at this
    · rw [Matrix.one_mulVec]
      exact hz _ (Or.inl (by simp [eI]))
  simp [psi, h]
end Formalism.QuantumDeterminants.BesselUnipotentEquiv
