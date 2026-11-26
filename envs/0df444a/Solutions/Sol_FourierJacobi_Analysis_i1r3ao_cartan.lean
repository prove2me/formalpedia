-- Prove2me | solution 1 for FourierJacobi.Analysis.i1r3ao_cartan
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:00:16.305199+00:00
-- url     : https://prove2.me/submissions/54d0faec-69ed-4dc6-ae02-81a2a20f9448

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
theorem _root_.solution (p : I1R3AORow) (depth : ℕ) :
    cartanIndices 1 p.val.1 p.val.2.1 p.val.2.2 depth = (2,-p.val.1-p.val.2.1-1) := by
  rw [← tableOne_correct _ _ _ _ (by omega)]
  rcases p with ⟨⟨k,j,h⟩,hp⟩
  dsimp at hp ⊢
  have hp0 : 1 ≤ k ∧ j < -2*k ∧ k+j ≤ h ∧ j ≤ 2*h := ⟨hp.1, hp.2.1, hp.2.2.1, hp.2.2.2.1⟩
  clear hp
  rw [tableOne, if_pos hp0.1, if_neg (by omega : ¬ -2*k ≤ j),
    if_neg (by omega : ¬ h < k+j)]
  rw [collisionRows, if_pos (by omega : j-1+1 ≤ 2*h)]
  norm_num
end FourierJacobi.Analysis
