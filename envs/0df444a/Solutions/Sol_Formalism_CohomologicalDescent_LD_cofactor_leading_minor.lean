-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LD.cofactor_leading_minor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:34:48.071045+00:00
-- url     : https://prove2.me/submissions/6b80e06b-9f96-4986-87bb-51376f194fa9

import Definitions.Def_Formalism_PieriBlockIdeals_LastGradedOfGradedAlone
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LastGradedImpliesOneBlock
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HighestWeightShiftEqDetMul
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LEhwLemmas
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HighestWeightProdLeadingMinors
import Theorems.Thm_Formalism_CohomologicalDescent_LD_jacobi_complementary_minor
import Theorems.Thm_Formalism_CohomologicalDescent_LD_ld3Gam_inl
import Theorems.Thm_Formalism_CohomologicalDescent_LD_ld3Gam_inr
import Theorems.Thm_Formalism_CohomologicalDescent_LD_cofactor_of_variable
import Theorems.Thm_Formalism_GradedWeylDivisibility_algHom_det_of
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
open MvPolynomial
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.LD
open Formalism.GradedWeylDivisibility Formalism.CohomologicalDescent.LA
namespace Formalism.CohomologicalDescent.LD
theorem _root_.solution {r s t : ℕ} (h : s + t = r) (hs : s ≤ r) (ht : t ≤ r) :
    genericDet ℤ r * cofMap r (lpMinor ℤ s hs hs) = genericDet ℤ r ^ s * lpMinor ℤ t ht ht := by
  have J := jacobi_complementary_minor (genericMatrix' ℤ r) (finSumEquivOfAddEq h) (finSumEquivOfAddEq h)
  have e1 : (Matrix.of fun i j : Fin s =>
      (genericMatrix' ℤ r).adjugate (finSumEquivOfAddEq h (Sum.inl j)) (finSumEquivOfAddEq h (Sum.inl i))).det =
        cofMap r (lpMinor ℤ s hs hs) := by
    unfold lpMinor
    rw [algHom_det_of]
    congr 1
    ext i j
    simp only [Matrix.of_apply, cofactor_of_variable, ld3Gam_inl]
  have e2 : (Matrix.of fun i j : Fin t => genericMatrix' ℤ r (finSumEquivOfAddEq h (Sum.inr i)) (finSumEquivOfAddEq h (Sum.inr j))).det =
      lpMinor ℤ t ht ht := by
    unfold lpMinor
    refine congrArg Matrix.det (Matrix.ext fun i j => ?_)
    simp only [Matrix.of_apply, ld3Gam_inr, genericMatrix']
  rw [e1, e2, Fintype.card_fin, Matrix.det_submatrix_equiv_self] at J
  exact J
end Formalism.CohomologicalDescent.LD
