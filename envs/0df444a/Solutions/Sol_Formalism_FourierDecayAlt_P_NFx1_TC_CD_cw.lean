-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.NFx1.TC.CD.cw
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T05:54:35.161962+00:00
-- url     : https://prove2.me/submissions/7d7ec057-4f3e-43d7-9b51-1c907f0588eb

import Definitions.Def_Formalism_HermitianCurvature_StatementNF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ActualAdjointnessFromHermitian
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumDualVectorEqZeta
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeylCellConjTransposeMulApply
import Definitions.Def_Formalism_FormalDegreeBessel_FinalWR
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelCoordinatesCommute
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx1_TC_diff_of_pres

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
namespace CD
theorem _root_.solution {T : (Mx k r → E) → Mx k r → E} (h : CD k r i T) : CW k r i T :=
  ⟨fun _ _ _ hΦ _ hx hg => diff_of_pres h.pres hΦ hx hg, h.comm⟩
end CD
end Formalism.FourierDecayAlt.P.NFx1.TC
