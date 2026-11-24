-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LD.cofactor_bideterminant
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:43:10.045801+00:00
-- url     : https://prove2.me/submissions/6d70a8e5-ec3e-4230-8004-a75ca17f8f38

import Definitions.Def_Formalism_PieriBlockIdeals_LastGradedOfGradedAlone
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LastGradedImpliesOneBlock
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HighestWeightShiftEqDetMul
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LEhwLemmas
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HighestWeightProdLeadingMinors
import Theorems.Thm_Formalism_CohomologicalDescent_LD_cofactor_initial_minor
import Theorems.Thm_Formalism_GradedWeylDivisibility_dualWeyl_prod
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
theorem _root_.solution {r K : ℕ} (sz : Fin K → ℕ) (hsz : ∀ k, sz k ≤ r) (I : ∀ k, Fin (sz k) → Fin r) :
    ∃ g ∈ dualWeyl ℤ r r (∑ k, initW r (r - sz k)),
      genericDet ℤ r ^ K * cofMap r (bideterminant ℤ sz hsz I) = genericDet ℤ r ^ (∑ k, sz k) * g := by
  choose g hg hg' using fun k => cofactor_initial_minor (Nat.add_sub_cancel' (hsz k)) (I k) (hsz k)
  refine ⟨∏ k, g k, dualWeyl_prod _ _ _ fun k _ => hg k, ?_⟩
  unfold bideterminant
  rw [map_prod, ← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]
  simp only [← hg']
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
end Formalism.CohomologicalDescent.LD
