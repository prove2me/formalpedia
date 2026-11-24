-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LD.dual_weyl_degree_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:21:22.991326+00:00
-- url     : https://prove2.me/submissions/cb84ec4d-c8a8-4111-88d4-81e42e00b864

import Definitions.Def_Formalism_PieriBlockIdeals_LastGradedOfGradedAlone
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LastGradedImpliesOneBlock
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HighestWeightShiftEqDetMul
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LEhwLemmas
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HighestWeightProdLeadingMinors
import Theorems.Thm_Formalism_CohomologicalDescent_LD_initial_minor_degree_le_one
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDeg_add
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDeg_zero
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_GradedWeylDivisibility_standardMonomialSpan
import Theorems.Thm_Formalism_GradedWeylDivisibility_support_prod_le_of_additive
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
theorem _root_.solution {r : ℕ} (ν : Fin r → ℕ) (hν : Antitone ν) (a : Fin r)
    (x : MvPolynomial (Fin r × Fin r) ℤ) (hx : x ∈ dualWeyl ℤ r r ν) :
    ∀ m ∈ x.support, rowDeg m a ≤ ν ⟨0, a.pos⟩ := by
  classical
  rw [standardMonomialSpan r r ν hν] at hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨K, sz, hsz, I, hshape, rfl⟩ := hx
    intro m hm
    have h := support_prod_le_of_additive (fun m => rowDeg m a) (rowDeg_zero a)
      (fun x y => rowDeg_add x y a) Finset.univ
      (fun k' => initMinor ℤ (I k') (hsz k')) (fun k' => if 0 < sz k' then 1 else 0)
      (fun k' _ m' hm' => initial_minor_degree_le_one (I k') (hsz k') a m' hm') m hm
    rw [← hshape]
    unfold shapeDeg
    rw [Finset.sum_boole] at h
    simpa using h
  | zero =>
    intro m hm
    simp at hm
  | add x y _ _ hx hy =>
    intro m hm
    rcases Finset.mem_union.mp (support_add hm) with h | h
    · exact hx m h
    · exact hy m h
  | smul c x _ hx =>
    intro m hm
    exact hx m (support_smul hm)
end Formalism.CohomologicalDescent.LD
