-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.PairingConjugationLemmas.covol_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:42:49.131255+00:00
-- url     : https://prove2.me/submissions/498b9987-8c21-4882-bfc6-4d62a6f6dcb8

import Definitions.Def_Formalism_HermitianCurvature_LatticeHerglotzBound
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HerglotzLowerSemicontinuous
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PairingTriangular
import Theorems.Thm_Formalism_FourierDecayAlt_P_PairingConjugationLemmas_map_fd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.PairingConjugationLemmas
open MeasureTheory Filter Topology Finset Module Formalism.FourierDecayAlt.crystallineComparison
noncomputable section
variable {f : ℕ}
variable (La : Submodule ℤ (V f)) [DiscreteTopology La] [IsZLattice ℝ La]
namespace Formalism.FourierDecayAlt.P.PairingConjugationLemmas
theorem _root_.solution (c : NNReal)
    (hc : (volume : Measure (V f)) = c • Measure.map (Tl La) (volume : Measure (Fin (finrank ℤ La) → ℝ))) :
    ZLattice.covolume La volume = (c : ℝ) := by
  have hfd := ZSpan.isAddFundamentalDomain (bR La) (volume : Measure (V f))
  rw [show Submodule.span ℤ (Set.range (bR La)) = La from
    Module.Basis.ofZLatticeBasis_span ℝ La _] at hfd
  rw [ZLattice.covolume_eq_measure_fundamentalDomain La volume hfd, hc, measureReal_def, Measure.smul_apply, map_fd]
  simp
end Formalism.FourierDecayAlt.P.PairingConjugationLemmas
