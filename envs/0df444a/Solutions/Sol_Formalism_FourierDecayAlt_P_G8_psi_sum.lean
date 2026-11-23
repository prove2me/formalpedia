-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.G8.psi_sum
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:07:59.625157+00:00
-- url     : https://prove2.me/submissions/dbc7f8ed-523c-411e-9e4e-2715592ce9d3

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_UnitaryInvariantGaussian
import Theorems.Thm_Formalism_FourierDecayAlt_P_G8_psi_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_G8_psi_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.G Matrix MeasureTheory Filter Topology
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.G8
namespace Formalism.FourierDecayAlt.P.G8
theorem _root_.solution {ι : Type} (β : ℂ) (s : Finset ι) (f : ι → ℂ) :
    psi β (∑ k ∈ s, f k) = ∏ k ∈ s, psi β (f k) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [psi_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, psi_add, ih]
end Formalism.FourierDecayAlt.P.G8
