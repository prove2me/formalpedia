-- Prove2me | solution 1 for Formalism.H.poissonSchwartz
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:09:20.593654+00:00
-- url     : https://prove2.me/submissions/e98c583a-1c19-4a55-b5a2-42789d14909c

import Definitions.Def_Formalism_LatticeTheta_LatticeThetaProofs_Assembly
import Definitions.Def_Formalism_LatticeTheta_LatticeThetaProofs_LatticeSummableDecay
import Definitions.Def_Formalism_LatticeTheta_LatticeThetaProofs_Periodization
import Definitions.Def_Formalism_LatticeTheta_LatticeThetaProofs_UnfoldCoeff
import Definitions.Def_Formalism_LatticeTheta_LatticeThetaProofs_LatticeFourierSeries
import Definitions.Def_Formalism_LatticeTheta_LatticeThetaProofs_GaussSchwartz
import Definitions.Def_Formalism_LatticeTheta_LatticeThetaProofs_DualLattice
import Definitions.Def_Formalism_LatticeTheta_LatticeThetaProofs_CovolumeDual
import Definitions.Def_Formalism_LatticeTheta_ThetaShiftInversion
import Theorems.Thm_Formalism_H_poissonDecay
import Theorems.Thm_Formalism_H_poissonSchwartz_of
import Theorems.Thm_Formalism_H_schwartz_decay_gaussian


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.H
variable (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
variable [MeasurableSpace V] [BorelSpace V]
namespace Formalism.H
theorem _root_.solution : PoissonSchwartz V := poissonSchwartz_of (poissonDecay V) (schwartz_decay_gaussian V)
end Formalism.H
