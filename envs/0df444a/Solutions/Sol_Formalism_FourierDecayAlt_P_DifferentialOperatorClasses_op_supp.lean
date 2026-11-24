-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.DifferentialOperatorClasses.op_supp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T19:24:27.971819+00:00
-- url     : https://prove2.me/submissions/263e8947-6d7f-429d-bf40-fbc70d6c45f7

import Definitions.Def_Formalism_HermitianCurvature_BigCellVanishingOfCommute
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HomogeneityNaturalDegree
import Mathlib.Topology.Algebra.MvPolynomial
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BigCellVanishingOfCommute
import Theorems.Thm_Formalism_FourierDecayAlt_P_DifferentialOperatorClasses_rw_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Filter Topology
noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.DifferentialOperatorClasses
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
namespace Formalism.FourierDecayAlt.P.DifferentialOperatorClasses
theorem _root_.solution (D : B.RealPlaceData k r Wp Wq) {ε : ℝ} (Θ : B.DiffOp k r Wp Wq) (G : B.Mat k r → (Wq →L[ℂ] Wp))
    (hG : ∀ g ∈ B.GV k r, G g ≠ 0 → ε ≤ Gf k r D.z D.z' g) :
    ∀ g ∈ B.GV k r, B.opApply Θ G g ≠ 0 → ε ≤ Gf k r D.z D.z' g := by
  intro g hg hne
  by_contra hlt
  push Not at hlt
  apply hne
  unfold B.opApply
  apply List.sum_eq_zero
  intro x hx
  obtain ⟨T, _, rfl⟩ := List.mem_map.1 hx
  rw [rw_zero D G hG T.word T.word_lie g hg hlt, map_zero]
end Formalism.FourierDecayAlt.P.DifferentialOperatorClasses
