-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Qx3.sf_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T16:01:33.744911+00:00
-- url     : https://prove2.me/submissions/e59a734e-f88b-452f-9830-7b5685b9fc8e

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexifiedDerivativeCommutator
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeylCellConjTransposeMulApply
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx3_sf_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx3_sf_add

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset Filter Topology
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Qx3
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable {i : Fin (r + 1)} {U₀ : Set (XX k r)}
namespace Formalism.FourierDecayAlt.P.Qx3
theorem _root_.solution {ι : Type*} (s : Finset ι) {Φ : ι → Fn k r E} (h : ∀ j ∈ s, SmoothFam k r i U₀ (Φ j)) :
    SmoothFam k r i U₀ (fun c g => ∑ j ∈ s, Φ j c g) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using sf_zero
  | insert a s ha ih =>
    have := sf_add (h a (Finset.mem_insert_self a s)) (ih fun j hj => h j (Finset.mem_insert_of_mem hj))
    simpa [Finset.sum_insert ha] using this
end Formalism.FourierDecayAlt.P.Qx3
