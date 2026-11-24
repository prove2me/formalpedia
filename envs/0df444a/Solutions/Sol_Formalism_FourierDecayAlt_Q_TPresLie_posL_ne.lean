-- Prove2me | solution 1 for Formalism.FourierDecayAlt.Q.TPresLie.posL_ne
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T16:56:42.660299+00:00
-- url     : https://prove2.me/submissions/6b6dc948-c78b-47f8-851c-456c55b74004

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MinorSmoothness_HasDerivAtExt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Q.TPresLie
open Formalism.REAL Formalism.QuantumDeterminants Formalism.QuantumDeterminants.GBasic Formalism.FourierDecayAlt.Q
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.Q.TPresLie
theorem _root_.solution (i : Fin (r + 1)) (q : Fin (mdim k r i)) (a : Fin r) (ha : a.val < i.val) :
    eI k r a ≠ posL k r i q ∧ esI k r a ≠ posL k r i q := by
  have hq := q.isLt
  have ha' := a.isLt
  unfold mdim at hq
  refine ⟨fun h => ?_, fun h => ?_⟩ <;>
  · have h2 := congrArg Fin.val h
    simp only [eI, esI, posL] at h2
    omega
end Formalism.FourierDecayAlt.Q.TPresLie
