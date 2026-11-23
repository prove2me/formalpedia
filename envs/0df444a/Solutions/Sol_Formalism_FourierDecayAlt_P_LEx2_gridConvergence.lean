-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.LEx2.gridConvergence
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:36:24.296177+00:00
-- url     : https://prove2.me/submissions/9314a896-17ae-4750-83f7-fc526caeb61b

import Definitions.Def_Formalism_HermitianCurvature_StatementLE
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MeasIterDeriv
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ThetaLimit
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeightedL2BoundedMul
import Theorems.Thm_Formalism_FourierDecayAlt_P_LEx2_interpN

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.LEx2
open Formalism.FourierDecayAlt.LE
open MeasureTheory Filter Topology Finset
namespace Formalism.FourierDecayAlt.P.LEx2
theorem _root_.solution : GridConvergence := by
  intro N n T l Q Q₀ grid hQ hQ0 hg hconv Y
  have h1 : ∀ t, MvPolynomial.eval Y (Q t) = ∑ g ∈ Fintype.piFinset grid,
      (∏ a, (Lagrange.basis (grid a) id (g a)).eval (Y a)) * MvPolynomial.eval g (Q t) :=
    fun t => interpN N n grid hg (Q t) (hQ t) Y
  rw [interpN N n grid hg Q₀ hQ0 Y]
  simp_rw [h1]
  apply tendsto_finset_sum
  intro g hgm
  exact (hconv g (fun a => (Fintype.mem_piFinset.1 hgm) a)).const_mul _
end Formalism.FourierDecayAlt.P.LEx2
