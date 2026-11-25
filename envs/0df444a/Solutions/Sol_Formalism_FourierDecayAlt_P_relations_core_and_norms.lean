-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.relations_core_and_norms
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:54:58.280815+00:00
-- url     : https://prove2.me/submissions/7fdcec9b-0df2-48d1-ae7e-26543d7b0161

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
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.NF.RelIsCoreNorm := by
  intro P A _ _ _ d
  unfold Formalism.FourierDecayAlt.Q.NFData.Rel Formalism.FourierDecayAlt.NF.RelCore Formalism.FourierDecayAlt.NF.RelNorm
  constructor
  · rintro ⟨h1, h2, h3, h4, h5, h6⟩
    exact ⟨⟨h1, h2, h3, h4, h5⟩, h6⟩
  · rintro ⟨⟨h1, h2, h3, h4, h5⟩, h6⟩
    exact ⟨h1, h2, h3, h4, h5, h6⟩
end Formalism.FourierDecayAlt.P
