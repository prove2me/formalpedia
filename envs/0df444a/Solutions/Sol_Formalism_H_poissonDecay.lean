-- Prove2me | solution 1 for Formalism.H.poissonDecay
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:02:22.22575+00:00
-- url     : https://prove2.me/submissions/9bdbeda4-12d8-4556-8abd-d3128b0ec7b4

import Definitions.Def_Formalism_LatticeTheta_LatticeThetaProofs_Assembly
import Definitions.Def_Formalism_LatticeTheta_LatticeThetaProofs_LatticeSummableDecay
import Definitions.Def_Formalism_LatticeTheta_LatticeThetaProofs_Periodization
import Definitions.Def_Formalism_LatticeTheta_LatticeThetaProofs_UnfoldCoeff
import Definitions.Def_Formalism_LatticeTheta_LatticeThetaProofs_LatticeFourierSeries
import Definitions.Def_Formalism_LatticeTheta_LatticeThetaProofs_GaussSchwartz
import Definitions.Def_Formalism_LatticeTheta_LatticeThetaProofs_DualLattice
import Definitions.Def_Formalism_LatticeTheta_LatticeThetaProofs_CovolumeDual
import Definitions.Def_Formalism_LatticeTheta_ThetaShiftInversion
import Theorems.Thm_Formalism_H_dualIsLattice
import Theorems.Thm_Formalism_H_lattice_fourier_series
import Theorems.Thm_Formalism_H_lattice_summable_decay
import Theorems.Thm_Formalism_H_poissonDecay_of
import Theorems.Thm_Formalism_H_poisson_periodization
import Theorems.Thm_Formalism_H_unfolding_fourier_coefficient


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
theorem _root_.solution : PoissonDecay V := poissonDecay_of (dualIsLattice V) (lattice_summable_decay V) (poisson_periodization V)
  (unfolding_fourier_coefficient V) (lattice_fourier_series V)
end Formalism.H
