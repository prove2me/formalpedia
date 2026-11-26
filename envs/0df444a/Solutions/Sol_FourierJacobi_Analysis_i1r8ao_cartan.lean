-- Prove2me | solution 1 for FourierJacobi.Analysis.i1r8ao_cartan
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:02:55.586545+00:00
-- url     : https://prove2.me/submissions/7dfbca7d-3692-4fd5-8317-d15e7a0a5fbf

import Definitions.Def_FourierJacobi_Analysis_MasterSeries
import Definitions.Def_FourierJacobi_Analysis_I1Complete
import Theorems.Thm_FourierJacobi_Analysis_i0NegativeRowEquiv_val
import Theorems.Thm_FourierJacobi_Analysis_masterTerm_zero
import Theorems.Thm_FourierJacobi_Analysis_shellMonomial_zero
import Theorems.Thm_FourierJacobi_Valuations_tableOne_correct
attribute [local simp] FourierJacobi.Analysis.i0NegativeRowEquiv_val
attribute [local simp] FourierJacobi.Analysis.masterTerm_zero
attribute [local simp] FourierJacobi.Analysis.shellMonomial_zero



set_option autoImplicit false
noncomputable section
open FourierJacobi FourierJacobi.Analysis
open FourierJacobi.Valuations
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
namespace FourierJacobi.Analysis
theorem _root_.solution (p : I1R8AORow) (depth : ℕ) :
    cartanIndices 1 p.val.1 p.val.2.1 p.val.2.2 depth = (2,-p.val.1-p.val.2.1-1) := by
  rw [← tableOne_correct _ _ _ _ (by omega)]
  rcases p with ⟨⟨k,j,h⟩,hp⟩
  dsimp at hp ⊢
  have hp0 : k ≤ 0 ∧ j < 0 ∧ j ≤ h ∧ j ≤ 2*h := ⟨hp.1, hp.2.1, hp.2.2.1, hp.2.2.2.1⟩
  clear hp
  rw [tableOne, if_neg (by omega : ¬ 1 ≤ k), if_neg (by omega : ¬ 0 ≤ j),
    if_neg (by omega : ¬ h < j)]
  rw [collisionRows, if_pos (by omega : j-1+1 ≤ 2*h)]
  norm_num
end FourierJacobi.Analysis
