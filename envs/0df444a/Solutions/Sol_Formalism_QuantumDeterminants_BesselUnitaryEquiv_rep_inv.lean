-- Prove2me | solution 1 for Formalism.QuantumDeterminants.BesselUnitaryEquiv.rep_inv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:03:01.161457+00:00
-- url     : https://prove2.me/submissions/ab0f41fe-a7d0-40fa-afec-e99c43cff436

import Definitions.Def_Formalism_FormalDegreeBessel_StatementBF
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_BesselUnitaryEquivHolds

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
open Formalism.QuantumDeterminants.BesselUnitaryEquiv
variable {k r : ℕ}
namespace Formalism.QuantumDeterminants.BesselUnitaryEquiv
theorem _root_.solution {W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W] {m : ℕ}
    {U : Set (Matrix (Fin m) (Fin m) ℂ)} {π : Matrix (Fin m) (Fin m) ℂ → (W →L[ℂ] W)}
    (hπ : IsCRepOn U π) {a b : Matrix (Fin m) (Fin m) ℂ} (ha : a ∈ U) (hb : b ∈ U)
    (hab : a * b = 1) (x : W) : π a (π b x) = x := by
  unfold IsCRepOn at hπ
  rw [← ContinuousLinearMap.comp_apply, ← hπ.2 a ha b hb, hab, hπ.1]
  try rfl
end Formalism.QuantumDeterminants.BesselUnitaryEquiv
