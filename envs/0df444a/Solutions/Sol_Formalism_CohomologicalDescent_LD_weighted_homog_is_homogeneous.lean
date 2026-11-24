-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LD.weighted_homog_is_homogeneous
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:27:20.506391+00:00
-- url     : https://prove2.me/submissions/bacef54e-8de5-422c-96f3-cab8e98d1be0

import Definitions.Def_Formalism_PieriBlockIdeals_LastGradedOfGradedAlone
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LastGradedImpliesOneBlock
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HighestWeightShiftEqDetMul
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LEhwLemmas
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HighestWeightProdLeadingMinors
import Theorems.Thm_Formalism_GradedWeylDivisibility_ldrow_weight_rowW
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
theorem _root_.solution {r : ℕ} (μ : Fin r → ℕ) (x : MvPolynomial (Fin r × Fin r) ℤ)
    (hx : IsWeightedHomogeneous (rowW r r) x μ) : x.IsHomogeneous (∑ a, μ a) := by
  intro d hd
  have hwt := hx hd
  have h1 : ∀ a, μ a = rowDeg d a := fun a => by rw [← ldrow_weight_rowW, hwt]
  simp only [h1, rowDeg]
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp), Fintype.sum_prod_type]
  simp
end Formalism.CohomologicalDescent.LD
