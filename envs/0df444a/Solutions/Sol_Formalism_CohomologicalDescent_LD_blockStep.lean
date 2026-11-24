-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LD.blockStep
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:46:24.723985+00:00
-- url     : https://prove2.me/submissions/78b8f950-9bb7-4e7f-9b07-5dac9b4ad1c6

import Definitions.Def_Formalism_PieriBlockIdeals_BranchingBoundLastGradedOneRow
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_DividedPowerZeroZeroVector
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LastGradedImpliesOneBlock
import Theorems.Thm_Formalism_CohomologicalDescent_LD_exp_le_of_nonzero_weight_vectors
import Theorems.Thm_Formalism_CohomologicalDescent_LD_depth_exists_last_block
import Theorems.Thm_Formalism_CohomologicalDescent_LD_restriction_eq_block_weight
import Theorems.Thm_Formalism_CohomologicalDescent_LD_restriction_antitone
import Theorems.Thm_Formalism_CohomologicalDescent_LD_expLeMono


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.LD
open Formalism.GradedWeylDivisibility
namespace Formalism.CohomologicalDescent.LD
theorem _root_.solution : BlockStep := by
  intro hD l n t lam hl ht ha hc eL heL I μ hμ
  have hres := restriction_eq_block_weight n t lam hc
  have hanti : Antitone (res n lam) := restriction_antitone n lam fun a b hab hb => ha a b hab (by omega)
  have hb : ∀ b : Fin n, lam n ≤ res n lam b ∧ res n lam b ≤ lam 0 := fun b =>
    ⟨ha b.val n (le_of_lt b.isLt) (by omega), ha 0 b.val (Nat.zero_le _) (by have := b.isLt; omega)⟩
  rw [hres] at hμ ⊢
  refine exp_le_of_nonzero_weight_vectors l _ _ μ _ hl fun x hx hne => ?_
  obtain ⟨i, hd, hi⟩ := depth_exists_last_block t n (lam n) (res n lam) hanti (fun b => (hb b).1) μ x hx hne
  have hμ' : depth2 (fun a : Fin (n + t) => if a.val < n then 1 else 0) (blockWtLast t n (lam n) (res n lam)) μ ≤
      (I : ℤ) := hμ
  rw [hi] at hμ'
  have hiI : i ≤ I := by exact_mod_cast hμ'
  have h1 := hD l t n (lam n) (lam 0) (res n lam) hl hanti hb eL heL i μ hd
  refine expLeMono l _ _ μ _ _ (Nat.add_le_add_left ?_ eL) h1
  unfold blockCost
  exact Finset.le_sup (f := fun i => padicValInt l (Dn t (lam 0 - lam n) i fun b : Fin n => lam 0 - res n lam (Fin.rev b)))
    (Finset.mem_range.mpr (by omega))
end Formalism.CohomologicalDescent.LD
