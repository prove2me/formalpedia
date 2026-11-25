-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.NFx1.TC.cd_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T04:50:38.533536+00:00
-- url     : https://prove2.me/submissions/52cd9f78-12b5-4893-9ab7-0d7259ba4cdf

import Definitions.Def_Formalism_HermitianCurvature_StatementNF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ActualAdjointnessFromHermitian
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumDualVectorEqZeta
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeylCellConjTransposeMulApply
import Definitions.Def_Formalism_FormalDegreeBessel_FinalWR
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelCoordinatesCommute

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
open Matrix Finset Filter Topology
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.NFx1 Formalism.FourierDecayAlt.P.NFx1.TC
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.NF
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {i : Fin (r + 1)}
namespace Formalism.FourierDecayAlt.P.NFx1.TC
theorem _root_.solution : CD k r i (fun _ : Mx k r → E => fun _ => (0 : E)) := by
  refine ⟨fun U₀ Φ _ x₀ _ _ => ⟨Set.univ, fun _ => (0 : E), isOpen_univ, trivial, contDiffOn_const, fun _ _ _ => rfl⟩,
    fun _ _ _ _ _ _ _ => rfl, ?_⟩
  intro U₀ _ Φ _ x _ _ v
  show fderiv ℝ (fun _ : Fin r → ℂ => (0 : E)) x.1 v = 0
  simp
end Formalism.FourierDecayAlt.P.NFx1.TC
