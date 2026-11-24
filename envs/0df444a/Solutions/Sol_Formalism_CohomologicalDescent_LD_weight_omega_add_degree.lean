-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LD.weight_omega_add_degree
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:18:23.651191+00:00
-- url     : https://prove2.me/submissions/ca2ece35-511b-426f-9603-a088699ba401

import Definitions.Def_Formalism_PieriBlockIdeals_LastGradedOfGradedAlone
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LastGradedImpliesOneBlock
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HighestWeightShiftEqDetMul
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LEhwLemmas
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HighestWeightProdLeadingMinors
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
theorem _root_.solution {r : ℕ} (d : Fin r × Fin r →₀ ℕ) (c : Fin r) :
    Finsupp.weight (diagonalEntryIndicator r) d c + rowDeg d (Fin.rev c) = ∑ a, rowDeg d a := by
  classical
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp), Finset.sum_apply, Fintype.sum_prod_type]
  have h1 : ∀ a : Fin r, ∑ s : Fin r, (d (a, s) • diagonalEntryIndicator r (a, s)) c = if a = Fin.rev c then 0 else rowDeg d a := by
    intro a
    have e : (c = Fin.rev a) ↔ (a = Fin.rev c) := by
      constructor <;> (intro h; rw [h, Fin.rev_rev])
    unfold rowDeg
    split_ifs with h
    · refine Finset.sum_eq_zero fun s _ => ?_
      simp [diagonalEntryIndicator, e.2 h]
    · refine Finset.sum_congr rfl fun s _ => ?_
      have h' : ¬ c = Fin.rev a := fun h' => h (e.1 h')
      simp [diagonalEntryIndicator, h']
  rw [Finset.sum_congr rfl fun a _ => h1 a]
  have h2 : rowDeg d (Fin.rev c) = ∑ a, if a = Fin.rev c then rowDeg d a else 0 := by simp
  rw [h2, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  split_ifs <;> simp
end Formalism.CohomologicalDescent.LD
