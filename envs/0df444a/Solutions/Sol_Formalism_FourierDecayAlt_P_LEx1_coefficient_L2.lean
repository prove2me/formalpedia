-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.LEx1.coefficient_L2
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:35:35.854841+00:00
-- url     : https://prove2.me/submissions/77790a73-eec6-401b-a1c3-e17fa3db0a47

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StepClaimFromStepsFull
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeightedL2ConstMul
import Theorems.Thm_Formalism_FourierDecayAlt_P_LEx1_weighted_L2_const_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_LEx1_weighted_L2_sum
import Theorems.Thm_Formalism_FourierDecayAlt_P_LEx1_extract

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.LEx1
open Formalism.FourierDecayAlt.LE
open MeasureTheory Filter Topology Finset
open scoped ComplexConjugate
namespace Formalism.FourierDecayAlt.P.LEx1
theorem _root_.solution : InterpolationCoefficientsInL2 := by
  intro B N d wt m c J hw hJ hm hL κ
  choose grid hsub hcard using fun a => (hJ a).exists_subset_card_eq (d + 1)
  have h : c κ = fun ω => ∑ g ∈ Fintype.piFinset grid,
      ((∏ a, (Lagrange.basis (grid a) id (g a)).coeff (κ a : ℕ) : ℝ) : ℂ) * m g ω := by
    funext ω
    rw [extract N d grid hcard (fun κ' => c κ' ω) κ]
    simp_rw [hm]
  rw [h]
  apply weighted_L2_sum B wt hw
  intro g hgm
  apply weighted_L2_const_mul
  apply hL
  intro a
  exact hsub a (Fintype.mem_piFinset.1 hgm a)
end Formalism.FourierDecayAlt.P.LEx1
